-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_first_distinct_row_scan
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.first_distinct_row_scan
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-25T04:48:12.736324+00:00
-- url     : https://prove2.me/theorems/f5f15fd2-892b-5748-97f7-2440883baf9b
-- title:
--   The duplicate-row scan recognizes the first seed for each block
-- statement:
--   Consider an $n$-point window, a seed $p$ in it, and its candidate block $C_p$. Suppose the preceding mask entries mark the least indices of their blocks, and the current row and those earlier marked rows contain their membership bits. The duplicate-row routine compares the current row with the marked earlier rows. At exit its flag is
--   $$\mathbf 1\{p=\min\{i\in W:C_i=C_p\}\}.$$
--   The routine preserves the heap, output, and closed flag and takes at most $600(n+1)^2$ machine steps. The statement permits arbitrary rows for earlier unmarked seeds.
-- source:
--   Native candidate enumeration in Appendix A.6, Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.first_distinct_row_scan
    (n b matrix mark : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (C : ℕ → Cluster n) (p : Fin n) (hp : p ∈ W)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (base : s.reg 165 = (b : ℤ))
    (mat : s.reg 80 = (matrix : ℤ)) (mask : s.reg 171 = (mark : ℤ))
    (seed : s.reg 173 = (p.val : ℤ)) (row : s.reg 176 = ((matrix+(b+p.val)*n : ℕ) : ℤ))
    (selected : ∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i ∈ representatives W C)
    (rows : ∀ i, i = p.val ∨ (i < p.val ∧ i ∈ representatives W C) →
      ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val) = if q ∈ C i then 1 else 0) :
    ∃ t k, Logical.Executes n m checkRepresentative s t k ∧ k ≤ 600*(n+1)^2 ∧
      t.reg 177 = (if p.val ∈ representatives W C then 1 else 0) ∧
      t.heap = s.heap ∧ t.output = s.output ∧ t.closed = s.closed
 := by sorry
