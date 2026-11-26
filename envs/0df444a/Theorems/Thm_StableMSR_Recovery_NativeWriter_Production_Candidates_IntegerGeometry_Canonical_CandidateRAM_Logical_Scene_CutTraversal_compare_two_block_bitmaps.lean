-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_compare_two_block_bitmaps
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.compare_two_block_bitmaps
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:07:13.320358+00:00
-- url     : https://prove2.me/theorems/2e343232-0801-4458-9f32-f1027ff5b94a
-- title:
--   Check overlap and equality of two block bitmaps in the compatibility test
-- statement:
--   The innermost counted loop of the actual compatibility routine visits every point. Starting from the fresh comparison flags, it returns the intersection and equality tests on the two represented blocks, preserves the heap and output, and uses at most 9 + 325n charged steps.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.compare_two_block_bitmaps (n L R : ℕ) (m : ℤ → ℤ) (s : Logical.State) (A B : ℕ → Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (left : s.reg 211=(L:ℤ)) (right : s.reg 213=(R:ℤ))
    (fresh : s.reg 214=0) (equal : s.reg 215=1)
    (bitsL : ∀i<n,s.heap (L+i)=if A i then 1 else 0)
    (bitsR : ∀i<n,s.heap (R+i)=if B i then 1 else 0) :
    ∃t k, Logical.Executes n m (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_fits 10)) 4)) 4)) 4)) 8) s t k ∧ k≤9+n*325 ∧
      t.reg 214=(if (List.range n).any (fun j=>A j && B j) then 1 else 0) ∧
      t.reg 215=(if (List.range n).all (fun j=>A j == B j) then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
