-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_fill_membership_row
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.fill_membership_row
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T04:48:45.895556+00:00
-- url     : https://prove2.me/theorems/9b8f5add-4aca-4363-9f53-b6888d543343
-- title:
--   The ball sweep writes the membership row of a candidate block
-- statement:
--   Let $p$ be a seed among $n$ points, $W$ a window, and $c=u(h+1)+g$ a candidate word with $0\leq g\leq h$. Supply the base-$n$ digits of $u$ and the membership bitmap of $W$ in cells disjoint from the destination row. Suppose destination cells outside $W$ start at zero. The per-seed sweep returns the exact bitmap
--   $$T[q]=\mathbf 1\{q\in \operatorname{block}(W,h,c,p)\},\qquad 0\leq q<n.$$
--   It preserves the rest of the heap, output and closed flag, and takes at most $4000(n+1)^2(h+1)$ steps. This includes words with no proper balls and arbitrary integer distance inputs.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.fill_membership_row
    (n h g u buf win dest : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (p : Fin n) (hg : g < h+1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (seed : s.reg 173 = (p.val : ℤ))
    (digitsAt : s.reg 166 = (buf : ℤ)) (balls : s.reg 169 = (g : ℤ))
    (window : s.reg 170 = (win : ℤ)) (row : s.reg 176 = (dest : ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j) = (CartesianBallRows.digit n u j : ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q ∈ W)
    (zeroOutside : ∀ q : Fin n, q ∉ W → s.heap (dest+q.val) = 0)
    (digitDisjoint : ∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j)
    (winDisjoint : ∀ i < n, ∀ j < n, dest+i ≠ win+j) :
    ∃ t k, Logical.Executes n m fillBlock s t k ∧ k ≤ 4000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, t.heap (dest+q.val) = if q ∈ Bits.block m W h (SingleCodes.encode h g u) p then 1 else 0) ∧
      (∀ z, z < dest ∨ dest+n ≤ z → t.heap z = s.heap z) ∧
      t.output = s.output ∧ t.closed = s.closed
 := by sorry
