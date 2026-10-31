-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P62_gaussian_distillable_iff_inseparable
-- name    : QAlgorithms.Papers.Independent.Intake100.P62.gaussian_distillable_iff_inseparable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:03:41.555067+00:00
-- url     : https://prove2.me/theorems/1b55a92e-a8a7-47e2-a302-0323760aaa46
-- title:
--   Every inseparable two-mode Gaussian state is distillable
-- statement:
--   The two parties each hold one complete oscillator mode, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$ and no occupation cutoff. A density means a positive trace-class operator of trace one. We use $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$.
--
--   Let $\rho$ be such a density whose Weyl characteristic is Gaussian, with arbitrary displacement and any physical covariance, including pure Gaussian states. Separability means membership in the trace-norm closed convex hull of product densities. Then
--
--   $$
--   \rho\text{ is distillable}\quad\Longleftrightarrow\quad\rho\text{ is inseparable}.
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
--   This identifies exactly which two-mode Gaussian states can supply finite-dimensional entanglement.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, PDF p. 1, Abstract and conclusion: all inseparable two-mode Gaussian states are distillable

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

/-- arXiv:quant-ph/0007061v2, PDF pp.1--4, abstract and conclusion:
all and only inseparable two-mode Gaussian oscillator densities are distillable.
No standardization, reduction violation or protocol is assumed. -/
theorem gaussian_distillable_iff_inseparable
    (rho : State (ℕ × ℕ))
    (hgaussian : ∃ V : Cov 2, GaussianWithCovariance (asFockKernel rho.coefficients) V) :
    HasFiniteOutputLOCCDistillation rho.coefficients ↔ ¬ IsSeparable rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intake100.P62

end
