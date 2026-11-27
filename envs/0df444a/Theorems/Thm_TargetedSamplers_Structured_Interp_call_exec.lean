-- Prove2me | Theorems.Thm_TargetedSamplers_Structured_Interp_call_exec
-- name    : TargetedSamplers.Structured.Interp.call_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:18.035198+00:00
-- url     : https://prove2.me/theorems/ad4273af-9f5a-4e10-80cf-16f29fcbc6f7
-- title:
--   Exact-cost simulation of a fixed RAM program by a structured interpreter
-- statement:
--   Exact-cost simulation of a fixed program by the structured interpreter.
--
--   Let $Q$ be a fixed RAM program and let the interpreter registers be distinct and nonzero. There is a constant $C$, depending only on $Q$ and the registers, with the following property. Suppose that $Q$, run on input $x$ with the coin window $(c_{\mathrm{co}},\dots,c_{\mathrm{co}+\mathrm{cl}-1})$ of the host coins (missing coins read as $0$), no witness and the zero oracle, halts in a state $\mathrm{st}$ of total cost at most $T$. Suppose the host store holds $x$ bitwise at $\mathrm{XB}$, the simulated region above $\mathrm{BIG}$ and the log area above $\mathrm{LOG}$ are zero, the layout satisfies
--   $$\mathrm{XB}+|x|\le \mathrm{LOG},\qquad \mathrm{LOG}+T+1\le \mathrm{BIG},$$
--   and the registers are initialized. Then `call r Q` terminates with exact cost at most
--   $$C\,(T+1)\,\bigl(\operatorname{size}(\mathrm{BIG}+\mathrm{co}+\mathrm{cl})+J+1\bigr),$$
--   records the last output bit of $\mathrm{st}$ in the capture register, and leaves every other host cell unchanged.
--
--   The cost is linear in the cost of the simulated run, which makes black-box use of a parity program possible inside a host algorithm.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search (Def_DirectedHamiltonicity_CycleSearch), supporting the formalization of Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), PDF pp. 2-5.

import Definitions.Def_LogCostRAM_Interpreter

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

theorem TargetedSamplers.Structured.Interp.call_exec (Q : Program) (r : IRegs) (hr : r.all.Nodup)
    (h0 : ∀ y ∈ r.all, y ≠ 0) :
    ∃ C : ℕ, ∀ (τ : Tapes) (J : ℕ) (x : List Bool) (co cl T BIG LOG XB : ℕ) (st : State) (S : Store),
      Q.final ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ = some st → st.work ≤ T →
      Cmd.FieldsFit J (call r Q) →
      S.mem r.pc = 0 → S.mem r.run = 1 → S.mem r.cnt = 0 → S.mem r.cap = 2 → S.mem r.one = 1 →
      S.mem r.zero = 0 → S.mem r.ds = 0 → S.mem r.t1 = 0 → S.mem r.t2 = 0 → S.mem r.t3 = 0 →
      S.mem r.t4 = 0 → S.mem r.t5 = 0 → S.mem r.t6 = 0 → S.mem 0 = 0 →
      S.mem r.big = BIG → S.mem r.logb = LOG → S.mem r.xb = XB → S.mem r.xlen = x.length →
      S.mem r.co = co → S.mem r.cl = cl →
      (∀ y ∈ r.all, y < XB) → XB + x.length ≤ LOG → LOG + T + 1 ≤ BIG →
      (∀ i (hi : i < x.length), S.mem (XB + i) = (x[i]'hi).toNat) →
      (∀ u, S.mem (BIG + u) = 0) → (∀ j, j ≤ T → S.mem (LOG + j) = 0) →
      ∃ S' k, WExec τ J (call r Q) S S' k ∧ k ≤ C * (T + 1) * ((BIG + co + cl).size + J + 1) ∧
        S'.mem r.cap = capValue st.out ∧ S'.mem r.run = 0 ∧ S'.out = S.out ∧
        ∀ y, y ≠ r.cap → y ≠ r.run → S'.mem y = S.mem y := by sorry
