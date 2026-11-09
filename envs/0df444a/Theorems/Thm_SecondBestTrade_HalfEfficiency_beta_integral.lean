-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_beta_integral
-- name    : SecondBestTrade.HalfEfficiency.beta_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:11.866385+00:00
-- url     : https://prove2.me/theorems/13fa782a-2508-44e5-84f9-d2b9dbd1384c
-- title:
--   Lemma 6.1 — Beta-integral bound
-- statement:
--   For every real $\tau\ge0$, put $\kappa=\tau/(1+\tau)$. The beta integrand is integrable and
--   $$\mathrm B(\tau)=\int_0^1u^{-\kappa}(1-u)^{-\kappa}\,du<2(1+\tau).$$
--   The inequality is strict, including at $\tau=0$, where the integral equals one. This is the exact factor used with the antithetic clocks.
--
--   Differences from the source:
--   - encoding: the convergent integral from zero to one → IntegrableOn and the same Lebesgue integral on the open interval (0,1); reason: removing endpoints changes no integral, and convergence is asserted so a default non-integrable value cannot supply the bound
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma 6.1 — Beta-integral bound, printed p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Clocks

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma 6.1, printed p. 12 (PDF p. 13); convergence is part of the conclusion. -/
theorem beta_integral (tau : ℝ) (htau : 0 ≤ tau) :
    IntegrableOn (betaIntegrand tau) (Set.Ioo (0 : ℝ) 1) ∧
    betaValue tau < 2 * (1 + tau) := by sorry

end SecondBestTrade.HalfEfficiency
