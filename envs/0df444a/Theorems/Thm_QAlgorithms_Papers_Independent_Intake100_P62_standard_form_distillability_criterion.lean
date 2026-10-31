-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P62_standard_form_distillability_criterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P62.standard_form_distillability_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:04:49.969944+00:00
-- url     : https://prove2.me/theorems/5602d37f-699b-4ea7-82ab-e3abe7b909cd
-- title:
--   Strict standard-form parameter criterion for distillability
-- statement:
--   The two parties each hold one complete oscillator mode, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$ and no occupation cutoff. A density means a positive trace-class operator of trace one. We use $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$.
--
--   Let $\rho$ be an actual centered Gaussian density with physical covariance
--
--   $$
--   M=\begin{pmatrix}
--   a&0&k_x&0\\
--   0&a&0&k_p\\
--   k_x&0&b&0\\
--   0&k_p&0&b
--   \end{pmatrix},\qquad k_x\ge |k_p|.
--   $$
--
--   Then
--
--   $$
--   \rho\text{ is distillable}\quad\Longleftrightarrow\quad
--   (ab-k_x^2)(ab-k_p^2)+1<a^2+b^2-2k_xk_p.
--   $$
--
--   Here distillable means that some fixed integer $d\ge2$ has the following property: for every $0<\epsilon<1$, finitely many independent copies admit local operations and classical communication with a strictly positive probability of producing a normalized state $\sigma_\epsilon$ such that
--
--   $$
--   \langle\Phi_d|\sigma_\epsilon|\Phi_d\rangle>1-\epsilon,
--   \qquad |\Phi_d\rangle=d^{-1/2}\sum_{j=0}^{d-1}|j,j\rangle.
--   $$
--
--   The copy number and success probability may depend on $\epsilon$; no uniform success bound or asymptotic rate is asserted.
--
--   This gives the source's scalar characterization for a density already in standard form. Physicality is a condition on the density and its characteristic function, rather than merely inequalities on four real numbers.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, PDF p. 2, Unnumbered parameter characterization, following (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P62

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex GaussianWithCovariance standardFormCovariance
   multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (conjugateKernel partialRight boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Bridge50.P18
  (HasCoefficients realizeCoefficients)

open QAlgorithms.Papers.Independent.Support50.P39 (noisyResourceCopies)

/-- arXiv:quant-ph/0007061v2, PDF p.2, (5)--(9): the explicit strict parameter
characterization for an actual physical density in centered standard form. -/
theorem standard_form_distillability_criterion
    (rho : State (ℕ × ℕ)) (a b kx kp : ℝ)
    (hstandard : CenteredStandard rho.coefficients a b kx kp)
    (horder : |kp| ≤ kx) :
    HasFiniteOutputLOCCDistillation rho.coefficients ↔ ParameterViolation a b kx kp := by sorry

end QAlgorithms.Papers.Independent.Intake100.P62

end
