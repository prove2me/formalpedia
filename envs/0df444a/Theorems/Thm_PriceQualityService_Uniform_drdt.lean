-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_drdt
-- name    : PriceQualityService.Uniform.drdt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:58.216419+00:00
-- url     : https://prove2.me/theorems/e1d64c3a-0f38-4646-aaec-9fdf474ba027
-- title:
--   $\partial r/\partial t=\sum_i A_iG_i/(1+\sum_i G_i)$ for the root of (24)
-- statement:
--   Let $c_i>0$ for every product, and let $R:\mathbb R\to\mathbb R$ satisfy $R(t)=\sum_{i\in\mathcal N}G_i(R(t),t)$ for every $t$, i.e. $R(t)$ is the root of (24) at the uniform duration $t$. Then $R$ is differentiable at every $t$ and
--   $$
--   \frac{\partial r}{\partial t}=R'(t)=\frac{\sum_{i\in\mathcal N}A_i(t)\,G_i(R(t),t)}{1+\sum_{i\in\mathcal N}G_i(R(t),t)},
--   $$
--   where $G_i(r,t)=\exp\big(b_i^2t^2/(4c_i)+(s_i-a_i+\alpha_ib_i/(2c_i))t+\alpha_i^2/(4c_i)-r-1\big)$ and $A_i(t)=s_i-a_i+\alpha_ib_i/(2c_i)+tb_i^2/(2c_i)$.
--
--   The sign of $\partial r/\partial t$ is the sign of its numerator, which is the quantity studied in the next step of the proof of Theorem 3.
--
--   **Formalization Note** $R$ is any function solving (24) pointwise; by the uniqueness in (24) there is exactly one such function, so the statement is about the paper's $r(t)$. Differentiability is part of the conclusion, not a hypothesis.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 29, Proof of Theorem 3, display after (24)

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

open Finset

/-- The implicit derivative of the root of (24) in the uniform duration, Proof of Theorem 3,
Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 29. If `R t` is, for every `t`, a root of
`r = ∑_i G_i(r, t)` with
`G_i(r, t) = exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i) − r − 1)`,
then `R` is differentiable at every `t` with `∂r/∂t = ∑_i A_i G_i / (1 + ∑_i G_i)`, where
`A_i = s_i − a_i + α_i b_i/(2c_i) + t b_i²/(2c_i)` and `G_i = G_i(R t, t)`. -/
theorem drdt {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) (t : ℝ) :
    HasDerivAt R
      ((∑ i, aTerm α a b c s t i * gTerm α a b c s (R t) t i)
        / (1 + ∑ i, gTerm α a b c s (R t) t i)) t := by sorry

end PriceQualityService.Uniform
