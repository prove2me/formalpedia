-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_logarithmicEqualityCriterion
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.logarithmicEqualityCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:36:52.540994+00:00
-- url     : https://prove2.me/theorems/58cb29f2-eaad-499f-9cdd-06d0467c0f84
-- title:
--   The finite matrix logarithmic equality criterion
-- statement:
--   Let $\sigma:M_b(\mathbb C)\to M_a(\mathbb C)$ be complex-linear, unital and $2$-positive, with $a,b\geq1$. Let $\omega$ and every member $\rho_\theta$ of a parameter family be strictly positive density matrices. Write $\sigma_*$ for the trace-dual density map, defined by $\operatorname{Tr}(\sigma_*(D)A)=\operatorname{Tr}(D\sigma(A))$, and let $D(\rho\Vert\omega)$ denote Umegaki relative entropy with natural logarithms. For every $\theta$,
--
--   $$D(\rho_\theta\Vert\omega)=D(\sigma_*(\rho_\theta)\Vert\sigma_*(\omega))\quad\Longleftrightarrow\quad\sigma\bigl(\log\sigma_*(\rho_\theta)-\log\sigma_*(\omega)\bigr)=\log\rho_\theta-\log\omega.$$
--
--   Induced logarithms are taken in their common support corner and extended by zero on its complement; $\sigma$ annihilates that complement. This characterizes equality in finite-dimensional entropy monotonicity.
--
--   **Source correction.** Inside $\sigma_*$ the printed density $D_{\omega_0}$ is replaced by $D_\omega$, since the dual map acts on densities of its codomain algebra. Independent moderation is required.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 14, Equation (12): logarithmic equality criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- Equation (12), PDF p.14, with an explicit source correction.
Printed: D_omega0 inside sigma_*; changed: D_omega, since sigma_* acts on
M-densities. Both input densities are strictly positive. The CFC logarithm
of each induced density is its true spectral logarithm in the common support
corner, extended by zero on the complement; sigma annihilates that complement.
No nonfaithful input-density logarithm formula is asserted. Independent moderation is required. -/
theorem logarithmicEqualityCriterion
    {I J : Type} {Theta : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ)
    (hSigma : IsCStarCoarseGraining sigma)
    (omega : Matrix I I ℂ) (rho : Theta → Matrix I I ℂ)
    (hOmega : QAlgorithms.IsDensityMatrix omega) (hOmegaFaithful : omega.PosDef)
    (hRho : ∀ theta, QAlgorithms.IsDensityMatrix (rho theta))
    (hRhoFaithful : ∀ theta, (rho theta).PosDef) :
    ∀ theta,
      (relativeEntropy (rho theta) omega =
        relativeEntropy (traceDensityDual sigma (rho theta)) (traceDensityDual sigma omega) ↔
      sigma (cfc Real.log (traceDensityDual sigma (rho theta)) -
        cfc Real.log (traceDensityDual sigma omega)) =
        cfc Real.log (rho theta) - cfc Real.log omega) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
