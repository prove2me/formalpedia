-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_sales_volume_mean
-- name    : SalesRebate.NoIncreasing.sales_volume_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:15.496067+00:00
-- url     : https://prove2.me/theorems/59fc5829-1f01-4892-ab81-3196aec76c01
-- title:
--   §II, display on p. 7 (PDF 7) — the ex-ante expected sales volume at any price x is Φ((θ−x)/σ)
-- statement:
--   In the Gaussian quality–taste model with $v \sim N(\theta, \sigma_\theta^2)$, $\sigma_\theta, \sigma_\epsilon > 0$ and $\sigma^2 = \sigma_\epsilon^2 + \sigma_\theta^2$, consumers with valuation above a price $x$ form, at quality $v$, a sales volume $\Phi((v-x)/\sigma_\epsilon)$. Its ex-ante expectation is, for every real $x$,
--   $$\mathbb E_v\Big[\Phi\Big(\frac{v - x}{\sigma_\epsilon}\Big)\Big] = \Phi\Big(\frac{\theta - x}{\sigma}\Big).$$
--
--   This identity turns the expected profit of a no-reward price $x$ into the closed form $x\Phi((\theta-x)/\sigma)$ that Assumption 1 optimizes.
--
--   **Formalization Note** The page states the identity at the market price $p$, before Assumption 1 fixes $p$; it is posed for every price $x$, because it is used both at $p$ and at an equilibrium cutoff $c$.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 7, §II, display Ev[ā(v)] = Ev[Φ((v−p)/σϵ)] = Φ((θ−p)/σ)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem sales_volume_mean (M : Model) (hM : M.Valid) (x : ℝ) :
    ∫ v, M.salesVolume x v ∂M.prior = stdNormalCDF ((M.θ - x) / M.σ) := by sorry

end SalesRebate.NoIncreasing
