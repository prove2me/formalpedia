-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_four_stack_transitions
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.four_stack_transitions
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-25T12:44:07.735884+00:00
-- url     : https://prove2.me/theorems/b4380525-f21a-406e-bbcc-877551ecd5a8
-- title:
--   The four transitions of the actual separator controller
-- statement:
--   One iteration of the actual while-loop advances the signed continuation index, pushes and visits an active separator, restores a completed parent, or stops at the root. The scratch arrays continue to represent the stack, and every iteration uses at most $850+V$ steps when one visit costs at most $V$.
-- source:
--   S. Ravichandran and L. Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.4 and A.6. Implementation lemma for the mission’s regional separator compiler.

import Definitions.Def_StableMSR_CutStackMoves
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.four_stack_transitions :
∀(d : SingleCircuit.Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z : Logical.State),
    0<d.n → Scene.CutTraversal.TraversalData d w z → (z.reg 8).toNat ≤ base →
    Scene.CutTraversal.Visits d w level m z V → Scene.CutTraversal.Moves d w level base m z V := by sorry
