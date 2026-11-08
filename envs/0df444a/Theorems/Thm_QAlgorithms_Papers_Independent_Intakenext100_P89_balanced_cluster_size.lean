-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_balanced_cluster_size
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.balanced_cluster_size
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:26:41.950303+00:00
-- url     : https://prove2.me/theorems/2e2eeb5d-4880-4372-8e4e-d0fe7743cb77
-- title:
--   Balanced binary fusion: photon count and inverse size budget
-- statement:
--   Consider the idealized balanced construction in which every leaf is a three-photon GHZ state and every successful Type-II fusion joins equal-size daughter clusters, consuming one photon from each daughter. Let $N_k$ be the photon-count budget after $k\in\mathbb N$ fusion levels, so $N_0=3$ and $N_{k+1}=2N_k-2$. Then
--
--   $$N_k=2^k+2.$$
--
--   For every integral target $N\ge3$, the exact inverse budget relation is
--
--   $$N\le N_k\quad\Longleftrightarrow\quad\lceil\log_2(N-2)\rceil\le k.$$
--
--   Thus the least depth whose budget reaches the target is $\lceil\log_2(N-2)\rceil$, encoded by Lean's `Nat.clog 2 (N - 2)`. This is the equal-daughter size-budget convention of the paragraph. It does not assert an optimal preparation schedule for every graph shape or the exact production of an arbitrary target graph.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 7, III.A: size and fusion-depth relation for the balanced construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source p.7, III.A: size in the idealized equal-daughter balanced construction and its
inverse size budget. For a target N >= 3, ceil(log_2(N-2)) is the least depth whose
photon-count budget reaches N. This is not an optimality claim about arbitrary graph
shapes or optical construction schedules. -/
theorem balanced_cluster_size (k : ℕ) :
    balancedSize k = 2 ^ k + 2 ∧
    (∀ N : ℕ, 3 ≤ N → (N ≤ balancedSize k ↔ Nat.clog 2 (N - 2) ≤ k)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
