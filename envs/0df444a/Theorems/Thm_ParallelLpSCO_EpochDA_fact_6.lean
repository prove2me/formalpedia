-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_fact_6
-- name    : ParallelLpSCO.EpochDA.fact_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:35.967347+00:00
-- url     : https://prove2.me/theorems/a58f2cf4-11c9-4ce6-8ce5-f91ecb4bd04d
-- title:
--   Fact 6 — Aggregate returns a point within $R$ of any $z$ that has at least $0.51k$ points within $R/3$, after $O(k^2)$ distance evaluations
-- statement:
--   Let $S=(y_1,\dots,y_k)$ with $y_i\in\mathbb R^d$ and $R>0$. Suppose some $z\in\mathbb R^d$ satisfies
--   $$|\{i\in[k]:\|y_i-z\|_p\le R/3\}|\ge0.51k.$$
--   Then $\mathrm{Aggregate}(S,R)$ (Algorithm 11) runs in $O(k^2d)$ time and returns $\tilde z\in S$ with $\|\tilde z-z\|_p\le R$.
--
--   Lemma 21 uses this to boost the $2/3$ success probability of one ball-oracle call to $1-\zeta$.
--
--   **Formalization Note.** The running time is counted as in the source's proof: at most $k^2$ pairwise ℓp distances, each costing $O(d)$ (`aggregateDistances`).
--
--   Differences from the source:
--   - reading: S = (y_1, …, y_k) (k unrestricted) → k ≥ 1; reason: the conclusion 'returns z̃ ∈ S' needs S nonempty; at k = 0 the hypothesis holds vacuously and nothing can be returned
--   - reading: runs in O(k²d) time → evaluates at most k² pairwise ℓp distances (each O(d)); reason: this is the proof's own accounting: 'at most O(k²) pairwise distance computations, each costing O(d) time'
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 93, Fact 6

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

namespace ParallelLpSCO.EpochDA

/-- Fact 6 (p. 93). If at least `0.51k` of the points `y_1, …, y_k` (`k ≥ 1`) lie within `R/3`
of some `z`, then Aggregate(S, R) evaluates at most `k²` pairwise ℓp distances and returns a point
`y_i` of `S` with `‖y_i − z‖_p ≤ R`. -/
theorem fact_6 (p : ℝ) (hp : 2 ≤ p) (d k : ℕ) (hk : 0 < k) (y : Fin k → Vec d) (R : ℝ)
    (hR : 0 < R) (z : Vec d)
    (hz : (51 / 100 : ℝ) * k ≤ ((Finset.univ.filter fun i => lpNorm p (y i - z) ≤ R / 3).card : ℝ)) :
    aggregateDistances p y R ≤ k ^ 2 ∧
      ∃ i, aggregate p y R = some i ∧ lpNorm p (y i - z) ≤ R := by sorry

end ParallelLpSCO.EpochDA
