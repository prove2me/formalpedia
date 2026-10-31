-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P62_infinite_dimensional_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P62.infinite_dimensional_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:05:56.050874+00:00
-- url     : https://prove2.me/theorems/5a744862-1fc5-4c96-8441-44619f8cd904
-- title:
--   Reduction violation implies distillability in infinite dimensions
-- statement:
--   The two parties each hold one complete oscillator mode, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$ and no occupation cutoff. A density means a positive trace-class operator of trace one. We use $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$.
--
--   Let $\rho$ be any such density, without a Gaussianity or energy assumption. Set $E(\rho)=(\operatorname{tr}_B\rho)\otimes I-\rho$, a bounded operator on the joint completed space. If a unit vector $\psi$ satisfies
--
--   $$
--   \operatorname{Re}\langle\psi|E(\rho)|\psi\rangle<0,
--   $$
--
--   then $\rho$ is distillable. Moreover, for some integer $N\ge1$, write $P_N=\sum_{k=0}^{N}|k\rangle\langle k|$ and $X_N=(P_N\otimes P_N)\rho(P_N\otimes P_N)$. The computed compression satisfies
--
--   $$
--   p_N=\operatorname{tr}X_N>0,\qquad \rho_N=X_N/p_N\text{ is a normalized distillable density}.
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
--   This extends the sufficient reduction criterion to the full separable infinite-dimensional Hilbert space and supplies a finite-dimensional postselected state.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, PDF p. 3, Extension of the reduction criterion to infinite dimensions

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

/-- arXiv:quant-ph/0007061v2, PDF pp.1,3, (1): extension of reduction to
infinite dimensions, including a computed positive-trace finite compression.
The witness is in H tensor H. No Gaussian or finite-moment assumption is made. -/
theorem infinite_dimensional_reduction
    (rho : State (ℕ × ℕ)) (psi : Hilbert (ℕ × ℕ))
    (hpsi : ‖psi‖ = 1) (hnegative : reductionExpectation rho.coefficients psi < 0) :
    HasCoefficients (reductionOperator rho.coefficients) (reductionKernel rho.coefficients) ∧
    HasFiniteOutputLOCCDistillation rho.coefficients ∧
    ∃ N : ℕ, 1 ≤ N ∧ 0 < branchTrace (bilateralNumberCutoff N rho.coefficients) ∧
      IsDensity (normalizeBranch (bilateralNumberCutoff N rho.coefficients)) ∧
      HasFiniteOutputLOCCDistillation (normalizeBranch (bilateralNumberCutoff N rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P62

end
