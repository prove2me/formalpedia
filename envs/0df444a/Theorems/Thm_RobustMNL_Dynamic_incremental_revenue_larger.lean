-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_incremental_revenue_larger
-- name    : RobustMNL.Dynamic.incremental_revenue_larger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:25.017977+00:00
-- url     : https://prove2.me/theorems/2b8df15c-3b87-4756-a4ea-9efcfcc47ea3
-- title:
--   Theorem 3.7 (restated) — additive incremental revenues lead to a larger robust assortment: S*(V) ⊆ S*_δ(V)
-- statement:
--   Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be compact and nonempty, let $r$ be arbitrary real revenues and $\delta \ge 0$. If $S$ is an optimal robust assortment of smallest cardinality for revenues $r$, and $S'$ is one for the revenues $r_i + \delta$, then
--   $$S^*(\mathcal V) = S \ \subseteq\ S' = S^*_\delta(\mathcal V).$$
--
--   In Section 4 this is used with $\delta = \Delta J_{t+1}(x) - \Delta J_{t+1}(x+1)$ (more capacity) and $\delta = \Delta J_{t+1}(x) - \Delta J_{t+2}(x)$ (a later period).
--
--   **Formalization Note** $Z^*_\delta, S^*_\delta$ (p. 10) are the static objects at revenues `fun i => r i + δ`, the same numbers as the paper's $\max_S\min_v\sum_{i\in S}(r_i+\delta)\phi_i(S,v)$. The uncertainty set is compact, nonempty, in $\mathbb R^{n+1}_{++}$ (Sec. 3 standing assumption); revenues are arbitrary reals. This restates `RobustMNL.Static.incremental_revenue_larger` of the companion mission verbatim up to namespace.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.7, p. 10 (Z*_δ, S*_δ defined on p. 10)

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_StaticModel

namespace RobustMNL.Dynamic

theorem incremental_revenue_larger {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, RobustMNL.Static.IsPos p) (δ : ℝ) (hδ : 0 ≤ δ)
    (S S' : Finset (Fin n)) (hS : RobustMNL.Static.IsSmallestOptimal V r S)
    (hS' : RobustMNL.Static.IsSmallestOptimal V (fun i => r i + δ) S') : S ⊆ S' := by sorry

end RobustMNL.Dynamic
