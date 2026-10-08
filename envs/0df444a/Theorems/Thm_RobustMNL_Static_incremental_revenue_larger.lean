-- Prove2me | Theorems.Thm_RobustMNL_Static_incremental_revenue_larger
-- name    : RobustMNL.Static.incremental_revenue_larger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:27.543984+00:00
-- url     : https://prove2.me/theorems/9bb84369-ca56-4ef6-a2e7-38476b160260
-- title:
--   Theorem 3.7 — additive incremental revenues lead to a larger robust assortment: S*(𝒱) ⊆ S*_δ(𝒱)
-- statement:
--   **Additive incremental revenues lead to a larger robust assortment.** Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be compact and nonempty and let $\delta \ge 0$. Let $S^*_\delta(\mathcal V)$ be an optimal assortment of smallest cardinality for the Robust Logit problem in which every revenue $r_i$ is replaced by $r_i + \delta$. Then
--   $$S^*(\mathcal V) \subseteq S^*_\delta(\mathcal V).$$
--
--   As the opportunity cost of not making a sale grows, the robust assortment grows. The paper uses this to compare the assortments of its dynamic model at different times and inventory levels.
--
--   **Formalization Note** The inclusion holds for every pair of smallest-cardinality optimal assortments $S$ (revenues $r$) and $S'$ (revenues $r + \delta$). The robust problem with revenues $r_i + \delta$ is the Robust Logit problem of the mission with the revenue vector `fun i => r i + δ`, since $\sum_{i\in S}(r_i+\delta)\phi_i(S,v)$ is $f(S, v)$ at those revenues. The set $\mathcal V$ is compact, nonempty and in $\mathbb R^{n+1}_{++}$, the standing assumption of Sec. 3. Revenues are arbitrary reals; products are `Fin n`.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.7, p. 10 (Z*_δ(V), S*_δ(V) defined on p. 10)

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem incremental_revenue_larger {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (δ : ℝ) (hδ : 0 ≤ δ)
    (S S' : Finset (Fin n)) (hS : IsSmallestOptimal V r S)
    (hS' : IsSmallestOptimal V (fun i => r i + δ) S') : S ⊆ S' := by sorry

end RobustMNL.Static
