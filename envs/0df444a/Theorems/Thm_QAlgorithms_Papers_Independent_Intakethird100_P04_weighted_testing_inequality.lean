-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P04_weighted_testing_inequality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P04.weighted_testing_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:51:30.723649+00:00
-- url     : https://prove2.me/theorems/cfc84a79-4d61-4c0f-9fd6-f8e763106779
-- title:
--   Weighted quantum testing inequality
-- statement:
--   Let $\rho,\sigma$ be positive trace-class operators of trace one on an arbitrary complex Hilbert space $H$. Choose complete orthonormal eigenbases $x_i,y_j$, including their kernels, with eigenvalues $\lambda_i,\gamma_j\ge0$. On $\Omega=\{(i,j)\}$ define $p(i,j)=\lambda_i|\langle x_i,y_j\rangle|^2$ and $q(i,j)=\gamma_j|\langle x_i,y_j\rangle|^2$. For every bounded Hermitian effect $0\le T\le I$ and every real $\delta>0$, put $\alpha[T]=1-\operatorname{Tr}(\rho T)$ and $\beta[T]=\operatorname{Tr}(\sigma T)$. Then
--
--   $$
--   \alpha[T]+\delta\beta[T]\ge\frac12\left(\sum_{\omega:p(\omega)\le\delta q(\omega)}p(\omega)+\delta\sum_{\omega:p(\omega)>\delta q(\omega)}q(\omega)\right).
--   $$
--
--   The two sums are nonnegative event masses; equality in the threshold belongs to the first event. This bound extends the projection comparison to every binary quantum test.
--
--   **Formalization Note** The inequality is embedded in the extended nonnegative reals. All its terms are finite for the stated states and effects, so this embedding preserves the exact real inequality.
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, PDF p. 4, Lemma 1, (18)–(19)

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

/-- Lemma 1, PDF p.4, (18), with spectral data from p.3, (12)--(13).
All bounded effects and delta>0 are permitted. The RHS factor is one half;
equality belongs to the p event. -/
theorem weighted_testing_inequality {I J L : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) (x : DensitySpectrum rho J) (y : DensitySpectrum sigma L)
    (T : Effect H) (delta : ℝ) (hdelta : 0 < delta) :
    (1 / 2 : ℝ≥0∞) *
        (lowerMass (spectralP x y) (spectralQ x y) (ENNReal.ofReal delta) +
          ENNReal.ofReal delta *
            upperMass (spectralP x y) (spectralQ x y) (ENNReal.ofReal delta)) ≤
      ENNReal.ofReal (1 - traceAcceptance b T.val rho.val.val) +
        ENNReal.ofReal delta * ENNReal.ofReal (traceAcceptance b T.val sigma.val.val) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P04

end
