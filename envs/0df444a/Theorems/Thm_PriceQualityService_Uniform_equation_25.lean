-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_equation_25
-- name    : PriceQualityService.Uniform.equation_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:51.096514+00:00
-- url     : https://prove2.me/theorems/162d56b8-62de-441c-a87d-37638ebad315
-- title:
--   (25): $r=y(t)/\exp(1+r)$, and the root of (24) increases with $y(t)$
-- statement:
--   Let $c_i>0$ for every product and put
--   $$
--   y(t)=\sum_{i\in\mathcal N}\exp\Big(\frac{b_i^2t^2}{4c_i}+\Big(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Big)t+\frac{\alpha_i^2}{4c_i}\Big).
--   $$
--
--   1. For all real $r$ and $t$, the root equation (24), $r=\sum_{i\in\mathcal N}G_i(r,t)$, holds if and only if
--   $$
--   r=\frac{y(t)}{\exp(1+r)}.\qquad(25)
--   $$
--   2. Consequently the root depends on $t$ only through $y(t)$, and monotonically: if $R(t)$ solves (24) for every $t$, then $y(t)\le y(t')$ implies $R(t)\le R(t')$.
--
--   This is the paper's alternative route to Theorem 3: maximizing the optimal profit over the uniform duration amounts to maximizing $y$.
--
--   **Formalization Note** The paper argues the monotonicity from the left side of (25) being increasing in $r$ and the right side strictly decreasing; part 2 states the resulting comparison for every pair of durations.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 29–30, Proof of Theorem 3, (25)

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

open Finset

/-- (25), Proof of Theorem 3, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), pp. 29–30.
(i) For all real `r`, `t`, the root equation (24) `r = ∑_i G_i(r, t)` is equivalent to
`r = y(t) / exp(1 + r)`, with `y(t) = ∑_i exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i))`.
(ii) Consequently the root depends on `t` only through `y(t)`, monotonically: if `R t` is a root
for every `t`, then `y(t) ≤ y(t')` implies `R t ≤ R t'`. -/
theorem equation_25 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ r t : ℝ, r = ∑ i, gTerm α a b c s r t i ↔ r = yTotal α a b c s t / Real.exp (1 + r)) ∧
    ∀ R : ℝ → ℝ, (∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) →
      ∀ t t' : ℝ, yTotal α a b c s t ≤ yTotal α a b c s t' → R t ≤ R t' := by sorry

end PriceQualityService.Uniform
