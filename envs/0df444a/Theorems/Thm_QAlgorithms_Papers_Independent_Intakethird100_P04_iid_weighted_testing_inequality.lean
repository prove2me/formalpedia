-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P04_iid_weighted_testing_inequality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P04.iid_weighted_testing_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:52:13.122204+00:00
-- url     : https://prove2.me/theorems/a40cec79-dc3b-4ea5-b8b7-88ec7f3fa77e
-- title:
--   Finite-block i.i.d. weighted testing inequality
-- statement:
--   Let $\rho,\sigma$ be density operators on an arbitrary complex Hilbert space, and let $p,q$ be the spectral probability weights $p(i,j)=\lambda_i|\langle x_i,y_j\rangle|^2$, $q(i,j)=\gamma_j|\langle x_i,y_j\rangle|^2$ from complete eigenbases of $\rho,\sigma$. For every positive integer $n$, every bounded effect $0\le T_n\le I$ on the completed tensor power $H^{\otimes n}$, and every $b\in\mathbb R$, define $\alpha_n=1-\operatorname{Tr}(\rho^{\otimes n}T_n)$, $\beta_n=\operatorname{Tr}(\sigma^{\otimes n}T_n)$ and the product laws $p^n(\omega_1,\ldots,\omega_n)=\prod_{t=1}^n p(\omega_t)$ and $q^n$ analogously. Set
--
--   $$
--   f_n(b)=\sum_{\omega:p^n(\omega)\le e^{-nb}q^n(\omega)}p^n(\omega),\qquad
--   g_n(b)=\sum_{\omega:p^n(\omega)>e^{-nb}q^n(\omega)}q^n(\omega).
--   $$
--
--   Then
--
--   $$
--   \alpha_n+e^{-nb}\beta_n\ge\frac12\bigl(f_n(b)+e^{-nb}g_n(b)\bigr).
--   $$
--
--   This is the finite-block comparison underlying the paper's large-deviation argument. The multiplicative events remain defined at zero spectral weights.
--
--   **Formalization Note** Lean index $k$ represents $n=k+1$. The completed tensor power is realized in its complete orthonormal coordinates $\ell^2(I^n)$ by the actual bounded operator with the tensor-product matrix coefficients.
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, PDF p. 4, §3, (20)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P04

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State operatorTrace relativeEntropy)

open QAlgorithms.Papers.Independent.Support50.P20
  (Effect traceAcceptance IsHilbertCPTP BlockHilbert blockBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)

variable {H K : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- PDF p.4, (20)--(22): i.i.d. weighted testing inequality. Index k denotes
n=k+1, and b is any real number. Multiplicative events include zero masses. -/
theorem iid_weighted_testing_inequality {I : Type} {J L : Type*}
    (basis : HilbertBasis I ℂ H) (rho sigma : State basis)
    (x : DensitySpectrum rho J) (y : DensitySpectrum sigma L)
    (k : ℕ) (T : Effect (BlockHilbert I k)) (b : ℝ) :
    let delta := ENNReal.ofReal (Real.exp (-((k + 1 : ℕ) : ℝ) * b))
    (1 / 2 : ℝ≥0∞) *
        (lowerMass (iidLaw (spectralP x y) k) (iidLaw (spectralQ x y) k) delta +
          delta * upperMass (iidLaw (spectralP x y) k) (iidLaw (spectralQ x y) k) delta) ≤
      ENNReal.ofReal (1 - traceAcceptance (blockBasis I k) T.val (iidOperator basis rho.val.val k)) +
        delta * ENNReal.ofReal
          (traceAcceptance (blockBasis I k) T.val (iidOperator basis sigma.val.val k)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P04

end
