-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_gaussianOUDecay
-- name    : QAlgorithms.Papers.Independent.Next46.P13.gaussianOUDecay
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:12:56.538483+00:00
-- url     : https://prove2.me/theorems/7dd614a1-c6ed-40cc-94d3-b29cccf77da5
-- title:
--   Appendix D, (79): Gaussian OU decay and optimality
-- statement:
--   Let $0<\lambda<\mu$, set $\zeta=\mu^2-\lambda^2$, and let $\Phi_t=e^{t(\mu^2L_-+\lambda^2L_+)}$ be the one-mode Ornstein–Uhlenbeck semigroup. Its stationary thermal state is $\sigma_{\mu,\lambda}=\omega_{\lambda^2/\zeta}$. Every Gaussian state $\rho$ with trivial kernel, allowing arbitrary first moments, has finite relative entropy and an existing right derivative satisfying
--
--   $$\left.\frac d{dt}D(\Phi_t(\rho)\Vert\sigma_{\mu,\lambda})\right|_{0+}
--   \le-\zeta D(\rho\Vert\sigma_{\mu,\lambda}),$$
--   $$D(\Phi_t(\rho)\Vert\sigma_{\mu,\lambda})\le
--    e^{-\zeta t}D(\rho\Vert\sigma_{\mu,\lambda})\qquad(t\ge0).$$
--
--   For every $\epsilon>0$ there is a positive-occupation thermal state $\omega_n$ of strictly positive relative entropy such that
--
--   $$\left.\frac d{dt}D(\Phi_t(\omega_n)\Vert\sigma_{\mu,\lambda})\right|_{0+}
--   >-(\zeta+\epsilon)D(\omega_n\Vert\sigma_{\mu,\lambda}).$$
--
--   Thus the Gaussian decay exponent is optimal. The strict witness is the one proved on p.34, and the all-state assertion on p.4 remains a conjecture.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 31, Appendix D, (79); pp.4,34

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.4,24,31–34, Appendix D, (79): arbitrary first moments are allowed.
Strict thermal witnesses follow the proof on p.34, excluding the vacuous fixed point. -/
theorem gaussianOUDecay (mu lambda : ℝ) (hmu : lambda < mu) (hlambda : 0 < lambda) :
    (∀ X : B.FockOperator, C.IsGaussian X → HasTrivialKernel X →
      quantumD X (stationaryState mu lambda) ≠ ⊤ ∧
      (∃ rate : ℝ, HasDerivWithinAt
        (fun t : ℝ => (quantumD (ou mu lambda t X) (stationaryState mu lambda)).toReal)
        rate (Set.Ici 0) 0 ∧ rate ≤ -ouDampingRate mu lambda * (quantumD X (stationaryState mu lambda)).toReal) ∧
      ∀ t : ℝ, 0 ≤ t →
        ThermalChannelRealized (Real.exp (-ouDampingRate mu lambda * t)) (stationaryMean mu lambda) X ∧
        quantumD (ou mu lambda t X) (stationaryState mu lambda) ≠ ⊤ ∧
        (quantumD (ou mu lambda t X) (stationaryState mu lambda)).toReal ≤
          Real.exp (-ouDampingRate mu lambda * t) * (quantumD X (stationaryState mu lambda)).toReal) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℝ, 0 < n ∧
      B.ThermalRealized (2 * n + 1) ∧ C.IsGaussian (C.photonMeanThermalState n) ∧ HasTrivialKernel (C.photonMeanThermalState n) ∧
      quantumD (C.photonMeanThermalState n) (stationaryState mu lambda) ≠ ⊤ ∧
      0 < quantumD (C.photonMeanThermalState n) (stationaryState mu lambda) ∧
      ∃ rate : ℝ, HasDerivWithinAt
        (fun t : ℝ => (quantumD (ou mu lambda t (C.photonMeanThermalState n)) (stationaryState mu lambda)).toReal)
        rate (Set.Ici 0) 0 ∧
        -(ouDampingRate mu lambda + epsilon) * (quantumD (C.photonMeanThermalState n) (stationaryState mu lambda)).toReal < rate) := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
