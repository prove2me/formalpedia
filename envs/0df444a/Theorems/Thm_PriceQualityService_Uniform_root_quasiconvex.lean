-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_root_quasiconvex
-- name    : PriceQualityService.Uniform.root_quasiconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:36.062892+00:00
-- url     : https://prove2.me/theorems/4aa3807e-1808-4dde-9dd9-12900db374fe
-- title:
--   The optimal profit $r(t)$ is quasi-convex in the uniform duration $t$
-- statement:
--   Let $c_i>0$ for every product and let $R:\mathbb R\to\mathbb R$ satisfy $R(t)=\sum_{i\in\mathcal N}G_i(R(t),t)$ for every $t$, so that $R(t)$ is the total expected profit at the optimal prices and qualities for the uniform duration $t$ (equation (24)). Then $R$ is quasi-convex on $\mathbb R$: for all $t,t'$ and $\lambda\in[0,1]$,
--   $$
--   R\big(\lambda t+(1-\lambda)t'\big)\le\max\{R(t),R(t')\}.
--   $$
--
--   In particular the maximum of $R$ over an interval $[t_s,t_l]$ is attained at $t_s$ or $t_l$, which is how the paper concludes Theorem 3.
--
--   **Formalization Note** Quasi-convexity is Mathlib's `QuasiconvexOn ℝ Set.univ R`, on the whole real line.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 29, Proof of Theorem 3

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

open Finset

/-- Proof of Theorem 3, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 29: the total
expected profit `r`, i.e. the root `R t` of (24) as a function of the uniform duration `t`,
is quasi-convex in `t` (on all of `ℝ`). -/
theorem root_quasiconvex {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) :
    QuasiconvexOn ℝ Set.univ R := by sorry

end PriceQualityService.Uniform
