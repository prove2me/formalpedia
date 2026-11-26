-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_compute_block_family_compatibility
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.compute_block_family_compatibility
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:14:08.398318+00:00
-- url     : https://prove2.me/theorems/2cc87c5f-eff0-560f-b0a4-831113d27a18
-- title:
--   Compute block-family compatibility in the regional table machine
-- statement:
--   The entire compatibility routine tests all selected pairs of blocks across two represented window families. The result is true precisely when every selected pair is disjoint or equal. It preserves the heap and output with a uniform cubic bound in the number of points plus a linear word-table charge.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.compute_block_family_compatibility (n M a b x y rep touch matrix : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (E F : ℕ→Bool) (A B : ℕ→Cluster n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (slots : s.reg 70=(M:ℤ))
    (ra : s.reg 203=(a:ℤ)) (rx : s.reg 204=(x:ℤ)) (rb : s.reg 205=(b:ℤ)) (ry : s.reg 206=(y:ℤ))
    (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ)) (mat : s.reg 80=(matrix:ℤ))
    (enabledA : ∀i<n,(1 ≤ s.heap (rep+((a*M+x)*n+i)) ∧ 1 ≤ s.heap (touch+((a*M+x)*n+i))) ↔ E i=true)
    (enabledB : ∀j<n,(1 ≤ s.heap (rep+((b*M+y)*n+j)) ∧ 1 ≤ s.heap (touch+((b*M+y)*n+j))) ↔ F j=true)
    (bitmapA : ∀i<n,E i=true → ∀p:Fin n,s.heap (matrix+(((a*M+x)*n+i)*n+p.val))=if p∈A i then 1 else 0)
    (bitmapB : ∀j<n,F j=true → ∀p:Fin n,s.heap (matrix+(((b*M+y)*n+j)*n+p.val))=if p∈B j then 1 else 0) :
    ∃t k, Logical.Executes n m src_fits s t k ∧ k≤1000*(M+1)+1000*(n+1)^3 ∧
      t.reg 217=(if (List.range n).all (fun i=> !E i || (List.range n).all (fun j=>
        !F j || decide (Disjoint (A i) (B j) ∨ A i=B j))) then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
