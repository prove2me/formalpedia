-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_y_convex
-- name    : PriceQualityService.Uniform.y_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:59.504501+00:00
-- url     : https://prove2.me/theorems/325244f4-e869-4a42-b6f4-92e912a1bd9f
-- title:
--   $y(t)=\sum_i\exp(\varphi_i(t))$ is convex in the uniform duration $t$
-- statement:
--   Let $c_i>0$ for every product. The function
--   $$
--   y(t)=\sum_{i\in\mathcal N}\exp\Big(\frac{b_i^2t^2}{4c_i}+\Big(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Big)t+\frac{\alpha_i^2}{4c_i}\Big)
--   $$
--   is convex on $\mathbb R$.
--
--   With (25), convexity of $y$ gives Theorem 3: the maximum of $y$, and hence of the optimal profit, over $[t_s,t_l]$ is attained at an endpoint.
--
--   **Formalization Note** The paper computes $\partial y/\partial t$ and $\partial^2y/\partial t^2$, with a stray $-r-1$ in the printed exponents and a claim "$>0$"; neither is needed, and only convexity (Mathlib's `ConvexOn ℝ Set.univ`) is stated.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 30, Proof of Theorem 3

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

/-- Proof of Theorem 3 (alternative proof), Wang, Ke & Cui, accepted manuscript (SSRN 3766191),
p. 30: `y(t) = ∑_i exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i))` is a
convex function of the service duration `t` on `ℝ`. -/
theorem y_convex {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ Set.univ (yTotal α a b c s) := by sorry

end PriceQualityService.Uniform
