-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_write_trial_close_record
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.write_trial_close_record
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:55:27.22627+00:00
-- url     : https://prove2.me/theorems/05ec1722-555c-49a1-bde4-d4b3bf7b5d76
-- title:
--   Write the local test result and clear its scratch cell
-- statement:
--   Assuming the local test result in the source flag, write exactly the close instruction with that bit and clear only the selected vertex scratch cell. Prove the charged cost, output counter, and full heap update.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_RegionalMenuImage
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.write_trial_close_record (n table v : ℕ) (m : ℤ→ℤ) (s : Logical.State) (ok : Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (tableAt : s.reg 225=(table:ℤ)) (vertex : s.reg 226=(v:ℤ))
    (result : s.reg 233=if ok then 1 else 0) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ)) :
    ∃t k, Logical.Executes n m (chain ((listOf src_trial).drop 13)) s t k ∧ k ≤ 300+n*(165+6*n) ∧
      (∀p,t.heap p=if p=table+v then 0 else s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++[Instr.close ok] := by sorry
