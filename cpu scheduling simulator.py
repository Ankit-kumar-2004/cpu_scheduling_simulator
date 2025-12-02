# cpu_scheduler_modern_final.py
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import random, itertools

# optional mplcursors
try:
    import mplcursors
    _HAS_MPLCURSORS = True
except Exception:
    _HAS_MPLCURSORS = False

# ---------------- helper visuals ----------------
def pid_color(pid):
    h = abs(hash(pid)) % (16**6)
    return "#{:06X}".format(h)

def text_contrast(hex_color):
    hex_color = hex_color.lstrip("#")
    r, g, b = int(hex_color[0:2],16), int(hex_color[2:4],16), int(hex_color[4:6],16)
    lum = 0.2126*r + 0.7152*g + 0.0722*b
    return "black" if lum > 150 else "white"

# ---------------- compute stats ----------------
def _compute_stats_from_gantt(gantt, processes):
    """
    [pid, arrival, burst, priority, completion, TAT, WT, RT]
    """
    proc_map = {p[0]: {"arrival": p[1], "burst": p[2], "priority": p[3]} for p in processes}
    done = []

    for pid in proc_map:
        segs = [s for s in gantt if s[0] == pid]
        if not segs:
            continue

        first_start = segs[0][1]
        completion = max(s[2] for s in segs)
        arrival = proc_map[pid]["arrival"]
        burst = proc_map[pid]["burst"]

        tat = completion - arrival
        wt = tat - burst
        rt = first_start - arrival

        done.append([pid, arrival, burst, proc_map[pid]["priority"],
                     completion, tat, wt, rt])

    done.sort(key=lambda x: x[0])
    return done

# ---------------- scheduling algorithms ----------------
def fcfs(processes):
    procs = sorted([p[:] for p in processes], key=lambda x: x[1])
    gantt = []
    time = 0
    for p in procs:
        if time < p[1]: time = p[1]
        start = time
        time += p[2]
        gantt.append((p[0], start, time))
    return gantt, _compute_stats_from_gantt(gantt, processes)

def sjf_nonpreemptive(processes):
    procs = sorted([p[:] for p in processes], key=lambda x: x[1])
    ready = []
    gantt = []
    time = 0
    while procs or ready:
        while procs and procs[0][1] <= time:
            ready.append(procs.pop(0))
        if ready:
            ready.sort(key=lambda x: x[2])
            p = ready.pop(0)
            start = time
            time += p[2]
            gantt.append((p[0], start, time))
        else:
            time = procs[0][1] if procs else time
    return gantt, _compute_stats_from_gantt(gantt, processes)

def sjf_preemptive(processes):
    # SRTF
    procs = sorted([p[:] for p in processes], key=lambda x: x[1])
    rem = {p[0]: p[2] for p in procs}
    ready = []
    gantt=[]
    time=0
    ai=0
    while ai<len(procs) or ready:
        while ai<len(procs) and procs[ai][1]<=time:
            ready.append(procs[ai]); ai+=1
        if not ready:
            time = procs[ai][1]; continue
        ready.sort(key=lambda x: rem[x[0]])
        p = ready[0]
        pid = p[0]
        start = time
        time+=1
        rem[pid]-=1
        if gantt and gantt[-1][0]==pid and gantt[-1][2]==start:
            gantt[-1]=(pid, gantt[-1][1], time)
        else:
            gantt.append((pid,start,time))
        if rem[pid]==0:
            ready=[r for r in ready if r[0]!=pid]
    return gantt, _compute_stats_from_gantt(gantt,processes)

def ljf_nonpreemptive(processes):
    # LONGEST JOB FIRST
    procs = sorted([p[:] for p in processes], key=lambda x: x[1])
    ready=[]; gantt=[]; time=0
    while procs or ready:
        while procs and procs[0][1]<=time:
            ready.append(procs.pop(0))
        if ready:
            ready.sort(key=lambda x: x[2], reverse=True)
            p=ready.pop(0)
            pid,at,bt,pr = p
            start=time
            time+=bt
            gantt.append((pid,start,time))
        else:
            time=procs[0][1] if procs else time
    return gantt,_compute_stats_from_gantt(gantt,processes)

def priority_nonpreemptive(processes):
    procs=sorted([p[:] for p in processes], key=lambda x:x[1])
    ready=[]; gantt=[]; time=0
    while procs or ready:
        while procs and procs[0][1]<=time:
            ready.append(procs.pop(0))
        if ready:
            ready.sort(key=lambda x:x[3])
            p=ready.pop(0)
            start=time
            time+=p[2]
            gantt.append((p[0],start,time))
        else:
            time=procs[0][1] if procs else time
    return gantt,_compute_stats_from_gantt(gantt,processes)

def priority_preemptive(processes):
    procs=sorted([p[:] for p in processes], key=lambda x:x[1])
    rem={p[0]:p[2] for p in procs}
    ready=[]; gantt=[]; time=0; ai=0
    while ai<len(procs) or ready:
        while ai<len(procs) and procs[ai][1]<=time:
            ready.append(procs[ai]); ai+=1
        if not ready:
            time=procs[ai][1]; continue
        ready.sort(key=lambda x:(x[3], rem[x[0]]))
        p=ready[0]; pid=p[0]
        start=time; time+=1; rem[pid]-=1
        if gantt and gantt[-1][0]==pid and gantt[-1][2]==start:
            gantt[-1]=(pid,gantt[-1][1],time)
        else:
            gantt.append((pid,start,time))
        if rem[pid]==0:
            ready=[r for r in ready if r[0]!=pid]
    return gantt,_compute_stats_from_gantt(gantt,processes)

def lrtf_preemptive(processes):
    # Longest Remaining Time First
    procs=sorted([p[:] for p in processes], key=lambda x:x[1])
    rem={p[0]:p[2] for p in procs}
    ready=[]; gantt=[]; time=0; ai=0
    while ai<len(procs) or ready:
        while ai<len(procs) and procs[ai][1]<=time:
            ready.append(procs[ai]); ai+=1
        if not ready:
            time=procs[ai][1]; continue
        ready.sort(key=lambda x:(-rem[x[0]], x[1]))
        p=ready[0]; pid=p[0]
        start=time; time+=1; rem[pid]-=1
        if gantt and gantt[-1][0]==pid and gantt[-1][2]==start:
            gantt[-1]=(pid,gantt[-1][1],time)
        else:
            gantt.append((pid,start,time))
        if rem[pid]==0:
            ready=[r for r in ready if r[0]!=pid]
    return gantt,_compute_stats_from_gantt(gantt,processes)

def round_robin(processes, quantum):
    if quantum<=0: quantum=1
    procs = sorted([p[:] for p in processes], key=lambda x:x[1])
    rem={p[0]:p[2] for p in procs}
    time=0; queue=[]; gantt=[]; ai=0; completed=set()
    total=len(procs)
    while len(completed)<total:
        while ai<len(procs) and procs[ai][1]<=time:
            queue.append(procs[ai]); ai+=1
        if not queue:
            time=procs[ai][1]; continue
        p=queue.pop(0); pid=p[0]
        start=time
        exec_t=min(quantum, rem[pid])
        time+=exec_t; rem[pid]-=exec_t
        if gantt and gantt[-1][0]==pid and gantt[-1][2]==start:
            gantt[-1]=(pid,gantt[-1][1],time)
        else:
            gantt.append((pid,start,time))
        while ai<len(procs) and procs[ai][1]<=time:
            queue.append(procs[ai]); ai+=1
        if rem[pid]==0:
            completed.add(pid)
        else:
            queue.append(p)
    return gantt,_compute_stats_from_gantt(gantt,processes)

# ---------------- main app ----------------
class CPUSchedulerApp:
    def __init__(self, root):
        self.root=root
        root.title("✨ CPU Scheduling Simulator — Modern")
        root.geometry("1300x820")
        root.configure(bg="#0b0d10")

        self.processes=[]
        self.last_gantt=[]
        self.last_done=[]

        self.dark=True
        self.is_playing=False
        self.play_index=0

        self._build_ui()

    def _build_ui(self):
        # HEADER
        header=tk.Frame(self.root, bg="#081018", pady=10)
        header.pack(fill="x")
        tk.Label(header,text="⚙️ CPU Scheduling Simulator",
                 font=("Segoe UI",18,"bold"), bg="#081018", fg="#7EF0FF").pack(side="left", padx=14)

        # INPUT AREA
        main=tk.Frame(self.root,bg="#0b0d10")
        main.pack(fill="both",expand=False,padx=12,pady=(8,4))

        left=tk.Frame(main,bg="#0b0d10",width=360)
        left.pack(side="left",fill="y", padx=(0,10))

        card_input=tk.LabelFrame(left,text="Process Input",bg="#0b0d10",fg="#BFF3FF")
        card_input.pack(fill="x",pady=6)

        labels=["PID","Arrival","Burst","Priority"]
        self.entries={}
        for i,l in enumerate(labels):
            tk.Label(card_input,text=l,bg="#0b0d10",fg="#BFF3FF").grid(row=0,column=i,padx=4)
            e=tk.Entry(card_input,width=8,bg="#0f1113",fg="#e8ffff")
            e.grid(row=1,column=i,padx=4,pady=4)
            self.entries[l]=e

        btns=tk.Frame(left,bg="#0b0d10"); btns.pack(pady=6)
        self._btn(btns,"➕ Add",self.add_process).pack(side="left",padx=5)
        self._btn(btns,"✏️ Edit",self.edit_selected).pack(side="left",padx=5)
        self._btn(btns,"🗑 Delete",self.delete_selected).pack(side="left",padx=5)

        misc=tk.Frame(left,bg="#0b0d10"); misc.pack(pady=6)
        self._btn(misc,"🎲 Random",self.add_random).pack(side="left",padx=5)
        self._btn(misc,"🧹 Clear",self.clear_all).pack(side="left",padx=5)
        self._btn(misc,"🌗 Theme",self.toggle_theme).pack(side="left",padx=5)

        # Controls
        card_ctrl=tk.LabelFrame(left,text="Simulation Controls",bg="#0b0d10",fg="#BFF3FF")
        card_ctrl.pack(fill="x",pady=6)

        tk.Label(card_ctrl,text="Algorithm",bg="#0b0d10",fg="#BFF3FF").grid(row=0,column=0,sticky="w")
        self.algo_var=tk.StringVar(value="FCFS")
        algo_list=[
            "FCFS",
            "SJF (Non-Preemptive)",
            "SJF (Preemptive)",
            "LJF (Non-Preemptive)",
            "Priority (Non-Preemptive)",
            "Priority (Preemptive)",
            "LRTF (Preemptive)",
            "Round Robin"
        ]
        ttk.Combobox(card_ctrl,textvariable=self.algo_var,values=algo_list,width=30)\
            .grid(row=1,column=0,pady=6,sticky="w")

        qf=tk.Frame(card_ctrl,bg="#0b0d10"); qf.grid(row=2,column=0,sticky="w")
        tk.Label(qf,text="Quantum:",bg="#0b0d10",fg="#BFF3FF").pack(side="left")
        self.q_entry=tk.Entry(qf,width=6,bg="#0f1113",fg="#e8ffff"); self.q_entry.insert(0,"2")
        self.q_entry.pack(side="left",padx=6)

        run_bar=tk.Frame(card_ctrl,bg="#0b0d10"); run_bar.grid(row=3,column=0,pady=8,sticky="w")
        self._btn(run_bar,"▶ Run",self.run_simulation).pack(side="left",padx=5)
        self._btn(run_bar,"⏯ Play",self.toggle_play).pack(side="left",padx=5)
        self._btn(run_bar,"🖼 Save Chart",self.save_chart).pack(side="left",padx=5)

        # TABLE SECTION
        center=tk.Frame(main,bg="#0b0d10")
        center.pack(side="left",fill="both",expand=True)

        p_card=tk.LabelFrame(center,text="Processes",bg="#0b0d10",fg="#BFF3FF")
        p_card.pack(fill="both",padx=6,pady=6)

        cols=("PID","Arrival","Burst","Priority")
        self.table=ttk.Treeview(p_card,columns=cols,show="headings",height=7)
        for c in cols:
            self.table.heading(c,text=c); self.table.column(c,width=100,anchor="center")
        self.table.pack(fill="both",expand=True)
        self.table.bind("<Delete>",lambda e:self.delete_selected())

        s_card=tk.LabelFrame(center,text="Stats",bg="#0b0d10",fg="#BFF3FF")
        s_card.pack(fill="x",padx=6,pady=(6,0))

        self.stats=ttk.Treeview(s_card,columns=("PID","CT","TAT","WT","RT"),show="headings",height=6)
        for c in ("PID","CT","TAT","WT","RT"):
            self.stats.heading(c,text=c); self.stats.column(c,width=90,anchor="center")
        self.stats.pack(fill="x")

        # BOTTOM — Averages + Gantt
        bottom=tk.Frame(self.root,bg="#0b0d10")
        bottom.pack(fill="both",expand=True,padx=12,pady=(6,12))

        avg=tk.Frame(bottom,bg="#0b0d10"); avg.pack(fill="x",pady=(0,6))
        self.avg_tat=tk.Label(avg,text="Avg TAT: —",bg="#0b0d10",fg="#BFF3FF",font=("Segoe UI",11,"bold"))
        self.avg_wt=tk.Label(avg,text="Avg WT: —",bg="#0b0d10",fg="#BFF3FF",font=("Segoe UI",11,"bold"))
        self.avg_rt=tk.Label(avg,text="Avg RT: —",bg="#0b0d10",fg="#BFF3FF",font=("Segoe UI",11,"bold"))

        self.avg_tat.pack(side="left",padx=10)
        self.avg_wt.pack(side="left",padx=10)
        self.avg_rt.pack(side="left",padx=10)

        g_card=tk.LabelFrame(bottom,text="Gantt Chart",bg="#0b0d10",fg="#BFF3FF")
        g_card.pack(fill="both",expand=True)

        self.canvas_frame=tk.Frame(g_card,bg="#0b0d10")
        self.canvas_frame.pack(fill="both",expand=True)

        self.legend=tk.Frame(g_card,bg="#0b0d10")
        self.legend.pack(fill="x",pady=6)

    # ------------- BUTTON helper -------------
    def _btn(self,parent,text,cmd):
        return tk.Button(parent,text=text,command=cmd,
                         bg="#00D9FF",fg="#001218",
                         font=("Segoe UI",9,"bold"),bd=0,padx=8,pady=6)

    # ------------- PROCESS OPS -------------
    def add_process(self):
        try:
            pid=self.entries["PID"].get().strip() or f"P{len(self.processes)+1}"
            at=int(self.entries["Arrival"].get())
            bt=int(self.entries["Burst"].get())
            pr=int(self.entries["Priority"].get())
        except:
            messagebox.showerror("Invalid","Enter numeric values.")
            return
        base=pid;i=1
        while any(p[0]==pid for p in self.processes):
            pid=f"{base}_{i}";i+=1
        self.processes.append([pid,at,bt,pr])
        self.table.insert("", "end", values=(pid,at,bt,pr))
        for e in self.entries.values(): e.delete(0,tk.END)

    def add_random(self):
        idx=len(self.processes)+1
        pid=f"P{idx}"; at=random.randint(0,6); bt=random.randint(1,12); pr=random.randint(1,10)
        self.processes.append([pid,at,bt,pr])
        self.table.insert("", "end", values=(pid,at,bt,pr))

    def edit_selected(self):
        sel=self.table.selection()
        if not sel:
            messagebox.showinfo("Select","Select a process."); return
        item=sel[0]
        pid,at,bt,pr=self.table.item(item,"values")
        # load into fields
        self.entries["PID"].delete(0,tk.END); self.entries["PID"].insert(0,pid)
        self.entries["Arrival"].delete(0,tk.END); self.entries["Arrival"].insert(0,at)
        self.entries["Burst"].delete(0,tk.END); self.entries["Burst"].insert(0,bt)
        self.entries["Priority"].delete(0,tk.END); self.entries["Priority"].insert(0,pr)
        # remove from list
        self.processes=[p for p in self.processes if p[0]!=pid]
        self.table.delete(item)

    def delete_selected(self):
        sel=self.table.selection()
        if not sel: return
        for item in sel:
            pid=self.table.item(item,"values")[0]
            self.processes=[p for p in self.processes if p[0]!=pid]
            self.table.delete(item)

    def clear_all(self):
        self.processes=[]
        for w in self.table.get_children(): self.table.delete(w)
        for w in self.stats.get_children(): self.stats.delete(w)
        for w in self.canvas_frame.winfo_children(): w.destroy()
        for w in self.legend.winfo_children(): w.destroy()
        self.avg_tat.config(text="Avg TAT: —")
        self.avg_wt.config(text="Avg WT: —")
        self.avg_rt.config(text="Avg RT: —")

    # ------------- RUN SIMULATION -------------
    def run_simulation(self):
        if not self.processes:
            messagebox.showinfo("No Data","Add processes first."); return
        algo=self.algo_var.get()
        data=[p[:] for p in self.processes]

        try: q=int(self.q_entry.get())
        except: q=2

        if algo=="FCFS":
            g,d=fcfs(data)
        elif algo=="SJF (Non-Preemptive)":
            g,d=sjf_nonpreemptive(data)
        elif algo=="SJF (Preemptive)":
            g,d=sjf_preemptive(data)
        elif algo=="LJF (Non-Preemptive)":
            g,d=ljf_nonpreemptive(data)
        elif algo=="Priority (Non-Preemptive)":
            g,d=priority_nonpreemptive(data)
        elif algo=="Priority (Preemptive)":
            g,d=priority_preemptive(data)
        elif algo=="LRTF (Preemptive)":
            g,d=lrtf_preemptive(data)
        else:
            g,d=round_robin(data,q)

        self.last_gantt=g; self.last_done=d

        # stats table
        for w in self.stats.get_children(): self.stats.delete(w)
        for p in d:
            self.stats.insert("", "end",
                values=(p[0], p[4], p[5], p[6], p[7]))

        # averages
        avg_tat=sum(p[5] for p in d)/len(d)
        avg_wt=sum(p[6] for p in d)/len(d)
        avg_rt=sum(p[7] for p in d)/len(d)
        self.avg_tat.config(text=f"Avg TAT: {avg_tat:.2f}")
        self.avg_wt.config(text=f"Avg WT: {avg_wt:.2f}")
        self.avg_rt.config(text=f"Avg RT: {avg_rt:.2f}")

        self._draw_gantt(g)

    # ------------- DRAW GANTT -------------
    def _draw_gantt(self, gantt):
        for w in self.canvas_frame.winfo_children(): w.destroy()
        for w in self.legend.winfo_children(): w.destroy()

        fig=Figure(figsize=(12,4),dpi=100)
        ax=fig.add_subplot(111)

        pids=list(dict.fromkeys(s[0] for s in gantt))
        ymap={pid:i+1 for i,pid in enumerate(pids)}

        for pid in pids:
            col=pid_color(pid)
            tk.Label(self.legend,text=pid,bg=col,fg=text_contrast(col),
                     padx=6,pady=3).pack(side="left",padx=5)

        for pid,s,e in gantt:
            y=ymap[pid]
            col=pid_color(pid)
            ax.barh(y, e-s, left=s, color=col, edgecolor="black", height=0.6)
            ax.text((s+e)/2, y, pid, color=text_contrast(col), ha="center", va="center")

        ax.set_yticks(list(ymap.values()))
        ax.set_yticklabels(list(ymap.keys()))
        ax.set_xlabel("Time")
        ax.grid(axis='x',linestyle=':',alpha=0.5)

        ticks=sorted(set(itertools.chain.from_iterable([(s,e) for _,s,e in gantt])))
        ax.set_xticks(ticks)
        fig.tight_layout()

        canvas=FigureCanvasTkAgg(fig,master=self.canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill="both",expand=True)
        if _HAS_MPLCURSORS:
            try:mplcursors.cursor(ax.get_children(),hover=True)
            except:pass

    # ------------- PLAYBACK -------------
    def toggle_play(self):
        if not self.last_gantt: return
        self.is_playing=not self.is_playing
        if self.is_playing:
            self.play_index=0
            self._play_step()

    def _play_step(self):
        if not self.is_playing: return
        if self.play_index>=len(self.last_gantt):
            self.is_playing=False; return

        pid,s,e=self.last_gantt[self.play_index]
        for w in self.canvas_frame.winfo_children(): w.destroy()

        fig=Figure(figsize=(12,2),dpi=100)
        ax=fig.add_subplot(111)
        col=pid_color(pid)
        ax.barh(1,e-s,left=s,color=col,height=0.6)
        ax.set_yticks([]); ax.set_xlabel("Time")
        ax.set_xlim(max(0,s-2), e+2)
        canvas=FigureCanvasTkAgg(fig,master=self.canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill="both",expand=True)

        self.play_index+=1
        self.root.after(700,self._play_step)

    # ------------- MISC -------------
    def toggle_theme(self):
        # lightweight theme toggle
        self.dark=not self.dark
        bg="#0b0d10" if self.dark else "#EEE"
        self.root.configure(bg=bg)

    def save_chart(self):
        if not hasattr(self,"last_fig"):
            messagebox.showinfo("No chart","Run simulation first.")
            return
        path=filedialog.asksaveasfilename(defaultextension=".png")
        if not path: return
        self.last_fig.savefig(path, dpi=150)

# RUN APP
if __name__=="__main__":
    root=tk.Tk()
    app=CPUSchedulerApp(root)
    root.mainloop()