-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_optimal_ge_two_mul_sum_tail
-- name    : TSPHeuristics.Insertion.optimal_ge_two_mul_sum_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:32:24.475186+00:00
-- url     : https://prove2.me/theorems/5c4d1afb-09aa-4626-821b-f43f59b5acea
-- title:
--   Eq. (2.1) — OPTIMAL ≥ 2 Σ_{i=k+1}^{min(2k,n)} l_i
-- statement:
--   Let $(N,d)$ be a traveling salesman graph whose nodes are numbered $1,\dots,n$, and let $l_1\ge l_2\ge\dots\ge l_n$ be real numbers such that $d(p,q)\ge\min(l_p,l_q)$ for all distinct nodes $p,q$ (condition a) of Lemma 1). Then for every $k$ with $1\le k\le n$,
--   $$\mathrm{OPTIMAL}\ \ge\ 2\sum_{i=k+1}^{\min(2k,n)} l_i .$$
--
--   This is the key inequality in the proof of Lemma 1; summing it over $k=1,2,4,\dots$ yields the logarithmic bound.
--
--   **Formalization Note** Nodes are `Fin n` (0-based). A traveling salesman graph is `IsTSPDist d`: symmetric, nonnegative, triangle inequality, plus the normalization $d(i,i)=0$, which is not in the paper and does not affect any length, since a loop never enters a tour, subtour or insertion cost. Nodes are numbered $0,\dots,n-1$ in Lean, so the paper's range $k+1,\dots,\min(2k,n)$ becomes $k,\dots,\min(2k,n)-1$; the ordering $l_i\ge l_j$ for $i\le j$ (the proof's without-loss-of-generality numbering) is the hypothesis that $l$ is antitone. Condition a) is assumed for distinct nodes only (see Lemma 1).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 565, proof of Lemma 1, eq. (2.1)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (2.1), p. 565: if the numbers `l` are non-increasing in the node label (the WLOG ordering
of the proof of Lemma 1) and satisfy condition a) of Lemma 1, then for every `1 ≤ k ≤ n`,
`OPTIMAL ≥ 2 Σ_{i=k+1}^{min(2k,n)} l_i`. Nodes are 0-based, so the paper's indices
`k+1, …, min(2k, n)` are `k, …, min(2k, n) - 1` here. -/
theorem optimal_ge_two_mul_sum_tail {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (l : Fin n → ℝ) (hl : Antitone l)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val ∧ i.val < min (2 * k) n), l i
        ≤ TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
