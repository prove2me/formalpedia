-- Prove2me | Theorems.Thm_RobustMNL_Static_largest_optimal_robust
-- name    : RobustMNL.Static.largest_optimal_robust
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:48.56696+00:00
-- url     : https://prove2.me/theorems/377131a6-3262-4189-9862-d1a94297114e
-- title:
--   Theorem 3.6 — largest optimal assortment is robust: S*(𝒱) = ⋃_{v∈𝒱} S*_v
-- statement:
--   **The largest optimal assortment is robust.** Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be compact and nonempty. Then the smallest optimal robust assortment is the union of the optimal assortments under the individual parameter vectors in $\mathcal V$:
--   $$S^*(\mathcal V) = \bigcup_{v \in \mathcal V} S^*_v,$$
--   where $S^*_v = S^*(\{v\})$ is the optimal assortment of smallest cardinality when the parameters are known to equal $v$.
--
--   The robust assortment is thus the largest of the assortments that are optimal for some parameter vector in the uncertainty set.
--
--   **Formalization Note** For every smallest-cardinality optimal $S$ for $\mathcal V$ and every product $i$: $i \in S$ iff there are $v \in \mathcal V$ and a smallest-cardinality optimal $T$ for $\{v\}$ with $i \in T$. By Theorem 3.2 such a $T$ is unique, so "there is such a $T$" is the same as "for the $T$". The page writes "$\mathcal V \subseteq \mathbb R^n_{++}$"; it is read as compact nonempty $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ (the proof uses compactness). Revenues are arbitrary reals; products are `Fin n`.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.6, p. 10

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem largest_optimal_robust {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (hS : IsSmallestOptimal V r S) (i : Fin n) :
    i ∈ S ↔ ∃ p ∈ V, ∃ T : Finset (Fin n), IsSmallestOptimal {p} r T ∧ i ∈ T := by sorry

end RobustMNL.Static
