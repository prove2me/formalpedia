-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_window_partition_feasibility
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.window_partition_feasibility
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T21:15:14.222811+00:00
-- url     : https://prove2.me/theorems/a7c14f22-2385-4bb2-b75f-0c5e06a3bd2f
-- title:
--   The final window incidence scan computes canonical partition feasibility
-- statement:
--   Let $P$ be a list of candidate blocks on a window $W$ of an $n$-point instance. Suppose that the bitmap selects one representative of each distinct block, that its membership rows encode the blocks, and that the entering flag records their nonemptiness. The final four commands of the vertex program store the exact feasibility bit: every block is nonempty, distinct blocks are disjoint, and their union is $W$. For a menu of capacity $M$, this takes at most $$1000(n+1)^3+10(M+1)$$ charged operations. Exactly one heap entry is updated and the output is preserved.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.window_partition_feasibility
    (n b mark matrix win menu vertex M pos : ℕ) (m:ℤ→ℤ) (s:Logical.State)
    (W:Cluster n) (P:List (Cluster n)) (R:Finset ℕ) (C:ℕ→Cluster n)
    (rangeR:∀a∈R,a < n) (represented:P.toFinset=R.image C)
    (distinct:∀a∈R,∀z∈R,C a=C z → a=z)
    (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (base:s.reg 165=(b:ℤ)) (mask:s.reg 171=(mark:ℤ))
    (mat:s.reg 80=(matrix:ℤ)) (window:s.reg 170=(win:ℤ)) (dst:s.reg 81=(menu:ℤ))
    (vr:s.reg 162=(vertex:ℤ)) (len:s.reg 70=(M:ℤ)) (slot:s.reg 164=(pos:ℤ))
    (flag:s.reg 172=if ∀a∈R,(C a).Nonempty then 1 else 0)
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀p:Fin n,∀i∈R,1 ≤ s.heap (matrix+((b+i)*n+p.val)) ↔ p∈C i)
    (inside:∀p:Fin n,s.heap (win+p.val)=((if p∈W then 1 else 0:ℕ):ℤ)) :
    let ops:=Logical.listOf Logical.src_data_for_vertex
    ∃t k, Logical.Executes n m (Logical.chain (ops.drop (ops.length-4))) s t k ∧
      k ≤ 1000*(n+1)^3+10*(M+1) ∧
      t.heap=Function.update s.heap (menu+(vertex*M+pos)) (if Bits.feasible W P then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by sorry
