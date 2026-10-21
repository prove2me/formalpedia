-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_ouUniqueStationary
-- name    : QAlgorithms.Papers.Independent.Next46.P13.ouUniqueStationary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:14:08.927926+00:00
-- url     : https://prove2.me/theorems/ddb93f02-ae29-453f-affc-f9356d091199
-- title:
--   Unnumbered §§2.2,6: unique stationary OU thermal state
-- statement:
--   Let $0<\lambda<\mu$, let $\Phi_t=e^{t(\mu^2L_-+\lambda^2L_+)}$ be the one-mode Ornstein–Uhlenbeck semigroup for $t\ge0$, and put $\nu=\lambda^2/\mu^2$. Its unique stationary normalized positive trace-class state is
--
--   $$\sigma_{\mu,\lambda}=(1-\nu)\sum_{k\ge0}\nu^k|k\rangle\langle k|
--   =\omega_{\lambda^2/(\mu^2-\lambda^2)}.$$
--
--   Precisely, this Gaussian thermal density satisfies $\Phi_t(\sigma_{\mu,\lambda})=\sigma_{\mu,\lambda}$ for all $t\ge0$, and any normalized density fixed for all such times equals it. Uniqueness is among all states, with no Gaussian restriction. No negative-time completely positive maps are claimed.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 4, §§2.2,6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.4,23: unique stationary state of the canonical qOU semigroup.
Uniqueness is over all normalized states, including non-Gaussian states. -/
theorem ouUniqueStationary (mu lambda : ℝ) (hmu : lambda < mu) (hlambda : 0 < lambda) :
    B.IsDensity (stationaryState mu lambda) ∧ C.IsGaussian (stationaryState mu lambda) ∧
    B.HasFockMatrix (stationaryState mu lambda)
      (fun m n => if m = n then
        (((1 - lambda ^ 2 / mu ^ 2) * (lambda ^ 2 / mu ^ 2) ^ n : ℝ) : ℂ) else 0) ∧
    Stationary mu lambda (stationaryState mu lambda) ∧
    (∀ t : ℝ, 0 ≤ t → ThermalChannelRealized (Real.exp (-ouDampingRate mu lambda * t))
      (stationaryMean mu lambda) (stationaryState mu lambda)) ∧
    ∀ X : B.FockOperator, B.IsDensity X → Stationary mu lambda X → X = stationaryState mu lambda := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
