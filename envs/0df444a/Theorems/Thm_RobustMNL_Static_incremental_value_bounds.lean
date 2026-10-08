-- Prove2me | Theorems.Thm_RobustMNL_Static_incremental_value_bounds
-- name    : RobustMNL.Static.incremental_value_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:45.157572+00:00
-- url     : https://prove2.me/theorems/14483ac6-50ed-4927-bbe4-731d25ba03b1
-- title:
--   Proof of Theorem 3.7, p. 11 — Z*(𝒱) ≤ Z*_δ(𝒱) ≤ δ + Z*(𝒱) for δ ≥ 0
-- statement:
--   Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be compact and nonempty and let $\delta \ge 0$. Write $Z^*_\delta(\mathcal V)$ for the optimal value of the Robust Logit problem when every product revenue is increased by $\delta$,
--   $$Z^*_\delta(\mathcal V) = \max_{S\subseteq\mathcal A}\ \min_{v\in\mathcal V} \sum_{i\in S} (r_i + \delta)\,\phi_i(S, v).$$
--   Then
--   $$Z^*(\mathcal V) \le Z^*_\delta(\mathcal V) \le \delta + Z^*(\mathcal V).$$
--
--   Raising every revenue by $\delta$ raises the optimal worst-case revenue by at most $\delta$, because a customer buys at most one product. This sandwich yields Theorem 3.7.
--
--   **Formalization Note** Since $\sum_{i\in S}(r_i+\delta)\phi_i(S,v)$ is the expected revenue $f(S,v)$ computed with revenues $r_i + \delta$, $Z^*_\delta(\mathcal V)$ is written as `Zstar V (fun i => r i + δ)`. Revenues are arbitrary reals; products are `Fin n`.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Proof of Theorem 3.7, p. 11, line after the first display (Z*_δ(V) defined on p. 10)

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem incremental_value_bounds {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (δ : ℝ) (hδ : 0 ≤ δ) :
    Zstar V r ≤ Zstar V (fun i => r i + δ) ∧ Zstar V (fun i => r i + δ) ≤ δ + Zstar V r := by sorry

end RobustMNL.Static
