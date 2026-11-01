-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P45_greedyTradeoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P45.greedyTradeoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:25:13.707386+00:00
-- url     : https://prove2.me/theorems/4b4ceffd-0bdf-4c92-863f-c2a3b4f1b298
-- title:
--   Conditional shortest-path versus two-path threshold tradeoff
-- statement:
--   There exists a finite square-grid network with distinct terminals $a,b$ and a successful external subgraph $H$ with the following property. A shortest $a$–$b$ path $r$ leaves no further $a$–$b$ path when its edges are removed, whereas $H$ contains two edge-disjoint $a$–$b$ paths $s,t$ that are both longer than $r$. Write their edge lengths as $k_r,k_s,k_t$. There exists a threshold $\theta\in(0,1)$ such that the two conditional expected yields satisfy
--
--   $$q^{k_s-1}+q^{k_t-1}<q^{k_r-1}\quad(0<q<\theta),$$
--
--   $$q^{k_r-1}<q^{k_s-1}+q^{k_t-1}\quad(\theta<q\le1).$$
--
--   These are yields conditioned on the same external-success instance, before independent BSM outcomes. Each selected memory is used once, and terminals retain their halves. The result explains why shortest-path greedy need not maximize the one-slot conditional expected rate.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, PDF p. 5, §II.B.1: the shortest single path can lose to two longer disjoint paths

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF p.5: an external-success instance can favor either a shortest single
path or two longer disjoint paths, depending on `q`. The shortest choice
leaves no further path. The comparison is conditional on the same external
instance and thus has no external `p^k` factors. No witness coordinates are
specified in the source; the assertion is existential. -/
theorem greedyTradeoff :
    ∃ (N : ℕ) (G : GridNetwork N) (a b : Fin N) (H : Finset (Edge N))
      (r s t : PortTrailEncoding N) (theta : ℝ),
      a ≠ b ∧ H ⊆ physicalEdges G ∧
      r ∈ candidateRoutes H a b ∧ s ∈ candidateRoutes H a b ∧
      t ∈ candidateRoutes H a b ∧
      Function.Injective r.2 ∧ Function.Injective s.2 ∧ Function.Injective t.2 ∧
      (∀ u ∈ candidateRoutes H a b, routeLength r ≤ routeLength u) ∧
      candidateRoutes (H \ routeEdges r) a b = ∅ ∧
      Disjoint (routeEdges s) (routeEdges t) ∧
      routeLength r < routeLength s ∧ routeLength r < routeLength t ∧
      0 < theta ∧ theta < 1 ∧
      (∀ q : ℝ, 0 < q → q < theta →
        q ^ s.1.val + q ^ t.1.val < q ^ r.1.val) ∧
      (∀ q : ℝ, theta < q → q ≤ 1 →
        q ^ r.1.val < q ^ s.1.val + q ^ t.1.val) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P45
