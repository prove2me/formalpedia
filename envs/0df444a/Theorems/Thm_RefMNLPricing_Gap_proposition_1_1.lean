-- Prove2me | Theorems.Thm_RefMNLPricing_Gap_proposition_1_1
-- name    : RefMNLPricing.Gap.proposition_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.077749+00:00
-- url     : https://prove2.me/theorems/0fa56ae6-3f78-4c66-85c8-41358d44808f
-- title:
--   Proposition 1.1, p. 10 — V⋆ is non-decreasing in the price ceiling p_H and tends to ∞ as p_H → ∞
-- statement:
--   In the multi-product pricing model with reference effects under MNL demand ($b_i>0$, $c_i^\pm\ge0$), let $V^\star_{p_H}$ denote the optimal value function when prices are restricted to $[0,p_H]^n$. Suppose $0\le\alpha<1$, $0<\beta<1$, and $\max_{i\in N}c_i^+>0$. Fix an initial reference price $\mathbf r^0$ with nonnegative entries. Then:
--
--   1. $p_H\mapsto V^\star_{p_H}(\mathbf r^0)$ is non-decreasing on the ceilings $p_H>0$ with $\mathbf r^0\in[0,p_H]^n$;
--   2. the optimal value is unbounded in the ceiling:
--   $$\lim_{p_H\to\infty}V^\star_{p_H}(\mathbf r^0)=\infty.$$
--
--   The result shows that without a price ceiling the dynamic pricing problem is ill-posed when consumers respond to gains: a larger ceiling lets the seller raise the reference price and then sell at a perceived discount.
--
--   **Formalization Note** The paper says "for any initial reference price $\mathbf r^0$"; since the model has $\mathbf r^0\in[0,p_H]^n$, monotonicity is stated over the ceilings $p_H>0$ with $\mathbf r^0\in[0,p_H]^n$, and the limit is taken along all $p_H\to\infty$ (eventually every ceiling contains $\mathbf r^0$). The ceiling varies, so the standing assumption $p_H\ge\hat p_H$ of §2.4 is not imposed. The hypothesis $\max_i c_i^+>0$ is written as the existence of a product with $c_i^+>0$ (it requires $n\ge1$).
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 10, Proposition 1, item 1

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model

namespace RefMNLPricing.Gap

open Filter

/-- Proposition 1.1, p. 10: if `α < 1`, `β > 0` and `max_i c_i⁺ > 0`, then for an initial reference
price `r⁰ ≥ 0` the optimal value `V⋆(r⁰)` is non-decreasing in the price ceiling `p_H` (over the
ceilings with `r⁰ ∈ [0, p_H]ⁿ`) and tends to `+∞` as `p_H → ∞`. -/
theorem proposition_1_1 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hc : ∃ i, 0 < cp i)
    (r₀ : Fin n → ℝ) (hr₀ : ∀ i, 0 ≤ r₀ i) :
    MonotoneOn (fun pH => optValue a b cp cm α β pH r₀) {pH : ℝ | 0 < pH ∧ RefMNLPricing.Myopic.InBox pH r₀} ∧
      Tendsto (fun pH => optValue a b cp cm α β pH r₀) atTop atTop := by sorry

end RefMNLPricing.Gap
