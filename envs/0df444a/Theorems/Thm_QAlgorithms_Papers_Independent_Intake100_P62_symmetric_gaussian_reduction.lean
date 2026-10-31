-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P62_symmetric_gaussian_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P62.symmetric_gaussian_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:06:45.430986+00:00
-- url     : https://prove2.me/theorems/dd293634-e9ec-4195-91ac-c970a9fd9be8
-- title:
--   Symmetric Gaussian entanglement has a finite squeezing reduction witness
-- statement:
--   The two parties each hold one complete oscillator mode, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$ and no occupation cutoff. A density means a positive trace-class operator of trace one. We use $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$.
--
--   Let $\rho$ be a centered Gaussian density in physical standard form with $a=b=n$ and $k_x\ge|k_p|$. Define the normalized finite-squeezing vector
--
--   $$
--   |\psi_\lambda\rangle=\sqrt{1-\lambda^2}\sum_{k=0}^\infty\lambda^k|k,k\rangle,\qquad 0<\lambda<1,
--   $$
--
--   and let $E(\rho)=(\operatorname{tr}_B\rho)\otimes I-\rho$. The following conditions are equivalent:
--
--   1. $\rho$ is inseparable.
--   2. $(n-k_x)(n+k_p)<1$.
--   3. Some $\lambda\in(0,1)$ has $\langle\psi_\lambda|E(\rho)|\psi_\lambda\rangle<0$.
--   4. Some unit vector in the joint Hilbert space has negative reduction expectation.
--
--   In particular,
--
--   $$
--   \rho\text{ inseparable}\quad\Longrightarrow\quad\rho\text{ distillable}.
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
--   This supplies a genuine finite-squeezing Hilbert-space witness for the symmetric part of the argument.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, PDF p. 3, Symmetric Gaussian inseparability is equivalent to reduction violation

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

/-- arXiv:quant-ph/0007061v2, PDF pp.2--3, symmetric reduction theorem.
Finite squeezing replaces the non-Hilbert infinite EPR vector. The corrected
scalar test is (n-kx)(n+kp)<1; printed (12) is not assumed. -/
theorem symmetric_gaussian_reduction
    (rho : State (ℕ × ℕ)) (n kx kp : ℝ)
    (hstandard : CenteredStandard rho.coefficients n n kx kp)
    (horder : |kp| ≤ kx) :
    (¬ IsSeparable rho.coefficients ↔ (n-kx)*(n+kp)<1) ∧
    (¬ IsSeparable rho.coefficients ↔
      ∃ lambda : ℝ, 0 < lambda ∧ lambda < 1 ∧
        ‖squeezedLambdaWitness lambda‖ = 1 ∧
        reductionExpectation rho.coefficients (squeezedLambdaWitness lambda) < 0) ∧
    (¬ IsSeparable rho.coefficients ↔
      ∃ psi : Hilbert (ℕ × ℕ), ‖psi‖=1 ∧ reductionExpectation rho.coefficients psi < 0) ∧
    (¬ IsSeparable rho.coefficients → HasFiniteOutputLOCCDistillation rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P62

end
