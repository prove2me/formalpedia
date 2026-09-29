-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_lemma_1_sum_le_half_clog_add_one_mul_optimal
-- name    : TSPHeuristics.Insertion.lemma_1_sum_le_half_clog_add_one_mul_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:33:07.130723+00:00
-- url     : https://prove2.me/theorems/e37bf475-0cdf-46a5-89f5-8a66e402293f
-- title:
--   Lemma 1 — Σ l_p ≤ ½(⌈lg n⌉ + 1)·OPTIMAL
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n\ge1$ nodes, and assign to each node $p$ a real number $l_p$ such that
--
--   1. $d(p,q)\ge\min(l_p,l_q)$ for all distinct nodes $p$ and $q$, and
--   2. $l_p\le\tfrac12\,\mathrm{OPTIMAL}$ for all nodes $p$.
--
--   Then
--   $$\sum_{p\in N} l_p\ \le\ \tfrac12\bigl(\lceil\lg n\rceil+1\bigr)\,\mathrm{OPTIMAL},$$
--   where $\lg$ is the logarithm to base 2 and $\lceil x\rceil$ the least integer $\ge x$.
--
--   This lemma is the common engine of the paper's two logarithmic upper bounds: Theorem 1 (nearest neighbor) and Theorem 3 (every insertion method).
--
--   **Formalization Note** Nodes are `Fin n` (0-based). A traveling salesman graph is `IsTSPDist d`: symmetric, nonnegative, triangle inequality, plus the normalization $d(i,i)=0$, which is not in the paper and does not affect any length, since a loop never enters a tour, subtour or insertion cost. $\lceil\lg n\rceil$ is `Nat.clog 2 n` (so it is $0$ at $n=1$). The page states condition 1 "for all nodes $p$ and $q$"; with $p=q$ and $d(p,p)=0$ that would force every $l_p\le0$ and the lemma could no longer be applied in the proofs of Theorems 1 and 3. The proof uses condition 1 only on edges of a tour, whose endpoints are distinct, so it is stated for distinct nodes. No sign condition on $l$ is imposed, as on the page.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 565, Lemma 1

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Lemma 1, p. 565: if `d(p, q) ≥ min(l_p, l_q)` for all distinct nodes `p, q` and
`l_p ≤ OPTIMAL / 2` for all nodes `p`, then `Σ_p l_p ≤ ½(⌈lg n⌉ + 1) OPTIMAL`.
Condition a) is required for distinct nodes only (the page says "for all nodes p and q"; with
`p = q` it would force `l_p ≤ 0`, and the proof applies it only to edges of a tour). -/
theorem lemma_1_sum_le_half_clog_add_one_mul_optimal {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q)
    (hb : ∀ p, l p ≤ TSPHeuristics.Shared.optimal d / 2) :
    ∑ p, l p ≤ (1 / 2) * ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
