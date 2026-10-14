-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_willingness_to_pay_integrated
-- name    : SellingData.AppendsRotation.willingness_to_pay_integrated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:01.25339+00:00
-- url     : https://prove2.me/theorems/3015a4e6-8d1f-4df9-8311-355f9c6099cd
-- title:
--   Proof of Proposition 8, p. 33 — for c_i ≤ û, U_ij − U_i0 = −T_j + ∫_{v̲}^{c_i} H(v, α_j) dv
-- statement:
--   In the data-append model, let $\alpha\in(0,1)$ and $\underline v\le c\le\hat u$. For every fee $T$,
--   $$
--   \Big(-T+\int_{c}^{\bar v}(v-c)\,dH(v,\alpha)\Big)-\max\{\hat u-c,0\}=-T+\int_{\underline v}^{c}H(v,\alpha)\,dv .
--   $$
--
--   This is the integration-by-parts form of the marketer's willingness to pay for a data append when its cost lies below the prior mean. It makes the dependence on the cost and on the informativeness explicit: the derivative in $c$ is $H(c,\alpha)\ge0$, and the dependence on $\alpha$ runs through $\int_{\underline v}^{c}H(v,\alpha)\,dv$.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 33, proof of Proposition 8 (case c_i ≤ û)

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- Proof of Proposition 8, p. 33 (case `c_i ≤ û`): integrating by parts, a marketer's payoff from
the plan `(T, α)` relative to the outside option is `−T + ∫_{v̲}^{c} H(v, α) dv`. -/
theorem willingness_to_pay_integrated (M : Model) :
    ∀ α ∈ Ioo (0 : ℝ) 1, ∀ c ∈ Icc M.vLo M.uHat, ∀ T : ℝ,
      M.U c T α - M.outside c = -T + ∫ v in M.vLo..c, M.H v α := by sorry

end SellingData.AppendsRotation
