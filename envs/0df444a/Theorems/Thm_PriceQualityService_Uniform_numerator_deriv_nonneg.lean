-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_numerator_deriv_nonneg
-- name    : PriceQualityService.Uniform.numerator_deriv_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:37.162809+00:00
-- url     : https://prove2.me/theorems/0caa8133-11d9-4e34-9917-b0da163cfcad
-- title:
--   The numerator $\sum_i A_iG_i$ of $\partial r/\partial t$ has nonnegative derivative
-- statement:
--   Let $c_i>0$ for every product and let $R(t)$ be the root of (24) at every uniform duration $t$, as in the previous statement. Write $G_i=G_i(R(t),t)$ and $A_i=A_i(t)$. The numerator $n(t)=\sum_{i\in\mathcal N}A_i(t)\,G_i(R(t),t)$ of $\partial r/\partial t$ is differentiable at every $t$, with
--   $$
--   n'(t)=\sum_{i\in\mathcal N}\frac{b_i^2}{2c_i}G_i+\sum_{i\in\mathcal N}A_i^2G_i-\frac{\big(\sum_{i\in\mathcal N}A_iG_i\big)^2}{1+\sum_{i\in\mathcal N}G_i}\;\ge\;0 .
--   $$
--
--   Hence $n$ is nondecreasing, so $\partial r/\partial t$ changes sign at most once, from negative to positive; this is the step that makes $r$ quasi-convex in $t$.
--
--   **Formalization Note** The paper's display passes through a strict inequality "$>$" before reaching "$\ge 0$"; the strict step fails when every $A_i(t)=0$, so only the conclusion $n'(t)\ge0$ is stated.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 29, Proof of Theorem 3, derivative of the numerator

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

open Finset

/-- The derivative of the numerator of `∂r/∂t`, Proof of Theorem 3, Wang, Ke & Cui, accepted
manuscript (SSRN 3766191), p. 29. With `R` the root of (24) as a function of `t`,
`G_i = G_i(R t, t)` and `A_i = A_i(t)`, the numerator `n(t) = ∑_i A_i G_i` has derivative
`∑_i b_i²/(2c_i) G_i + ∑_i A_i² G_i − (∑_i A_i G_i)² / (1 + ∑_i G_i)` at every `t`, and this
derivative is nonnegative. (The paper prints a strict `>` in its first comparison; only `≥ 0`
holds in general and is what is stated.) -/
theorem numerator_deriv_nonneg {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) (t : ℝ) :
    let D : ℝ :=
      ∑ i, b i ^ 2 / (2 * c i) * gTerm α a b c s (R t) t i
        + ∑ i, aTerm α a b c s t i ^ 2 * gTerm α a b c s (R t) t i
        - (∑ i, aTerm α a b c s t i * gTerm α a b c s (R t) t i) ^ 2
          / (1 + ∑ i, gTerm α a b c s (R t) t i)
    HasDerivAt (fun u => ∑ i, aTerm α a b c s u i * gTerm α a b c s (R u) u i) D t ∧ 0 ≤ D := by sorry

end PriceQualityService.Uniform
