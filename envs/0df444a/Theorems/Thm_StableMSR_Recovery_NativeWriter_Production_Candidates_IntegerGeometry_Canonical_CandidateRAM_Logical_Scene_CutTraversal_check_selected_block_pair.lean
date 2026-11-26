-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_check_selected_block_pair
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.check_selected_block_pair
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:11:20.357463+00:00
-- url     : https://prove2.me/theorems/c96a99b1-b0b6-429c-8599-a3d86705bfce
-- title:
--   Apply the disjoint-or-equal test to one selected pair of blocks
-- statement:
--   The compatibility routine reads two represented blocks from the regional tables. For this selected pair the actual source keeps the running compatibility flag if the two blocks are disjoint or equal and clears it otherwise. It preserves the heap and output and has linear cost.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_VertexBlockRows
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.check_selected_block_pair (n R j L matrix : ℕ) (m : ℤ → ℤ) (s : Logical.State) (C D : Cluster n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (left : s.reg 211=(L:ℤ)) (base : s.reg 208=(R:ℤ)) (index : s.reg 212=(j:ℤ)) (mat : s.reg 80=(matrix:ℤ))
    (bitsL : ∀p : Fin n,s.heap (L+p.val)=if p∈C then 1 else 0)
    (bitsR : ∀p : Fin n,s.heap (matrix+((R+j)*n+p.val))=if p∈D then 1 else 0) :
    ∃t k, Logical.Executes n m (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_fits 10)) 4)) 4)) 4)) s t k ∧ k≤100+340*n ∧
      t.reg 209=(if Disjoint C D ∨ C=D then s.reg 209 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
