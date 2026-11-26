-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_prepare_trial_child_component
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.prepare_trial_child_component
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:41:12.684871+00:00
-- url     : https://prove2.me/theorems/17cc6827-c6c7-5d67-b12e-76b40a6417a6
-- title:
--   Store the trial label and remove its vertex from the component bitmap
-- statement:
--   The next four source commands store the selected word slot, allocate the child-search bitmap and fill it with the original component minus the chosen vertex. The proof specifies the entire new heap, the cursor, and preservation of the output.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.prepare_trial_child_component (n v word cp scratch dst : ℕ) (m : ℤ→ℤ) (s : Logical.State) (inComp : ℕ→Bool)
    (hv : v<n) (separate : cp+n ≤ scratch) (space : scratch+n ≤ dst)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(n:ℤ)) (cursor : s.reg 8=(dst:ℤ))
    (compAt : s.reg 223=(cp:ℤ)) (labelAt : s.reg 225=(scratch:ℤ))
    (vertex : s.reg 226=(v:ℤ)) (slot : s.reg 227=(word:ℤ))
    (bits : ∀q<n,s.heap (cp+q)=if inComp q then 1 else 0) :
    ∃t k, Logical.Executes n m (chain (((listOf src_trial).drop 5).take 4)) s t k ∧ k ≤ 200+300*n ∧
      t.reg 230=(dst:ℤ) ∧ t.reg 8=((dst+n:ℕ):ℤ) ∧ t.output=s.output ∧ t.closed=s.closed ∧
      ∀p,t.heap p=if dst ≤ p ∧ p<dst+n then (if inComp (p-dst) && decide (p-dst≠v) then 1 else 0)
        else if p=scratch+v then (word:ℤ) else s.heap p := by sorry
