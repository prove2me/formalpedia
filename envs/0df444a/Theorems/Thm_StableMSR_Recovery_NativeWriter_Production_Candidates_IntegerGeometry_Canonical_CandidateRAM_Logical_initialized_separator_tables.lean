-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_initialized_separator_tables
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.initialized_separator_tables
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:28:53.961782+00:00
-- url     : https://prove2.me/theorems/9d80a147-4351-4e01-a5c2-4c6b1bf52877
-- title:
--   The actual generator initializes every separator table at its specified address
-- statement:
--   From arbitrary input scratch contents the concrete 45-command source prefix computes $H=h+1$, $R=n^{2H}$ and $M=HR$. Its eleven array bases are exactly the respective prefix sums. Every allocated word is zero, the suffix is untouched, and the stream and closing flag are preserved. Its source charge is at most $4000(h+2)(n+1)^3(M+1)$.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_SeparatorArenaLayout
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.initialized_separator_tables (n h:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (start:s.reg 8=0) (sz:s.reg 64=(n:ℤ)) (budget:s.reg 66=(h:ℤ)) :
    let H:=h+1
    let rows:=n^(2*H)
    let M:=H*rows
    let layout:=offsets n M
    ∃t z,Executes n input arena s t z ∧ z ≤ 4000*(h+2)*(n+1)^3*(M+1) ∧
      t.reg 68=(H:ℤ) ∧ t.reg 69=(rows:ℤ) ∧ t.reg 70=(M:ℤ) ∧ t.reg 82=0 ∧
      t.reg 8=(cursorAt layout 11:ℤ) ∧
      (∀j:Fin 11,t.reg (71+j.val)=(cursorAt layout j.val:ℤ)) ∧
      ((∀i,t.heap i=if i<cursorAt layout 11 then 0 else s.heap i) ∧ t.output=s.output ∧ t.closed=s.closed) ∧ (∀j<68,j≠8 → t.reg j=s.reg j) := by sorry
