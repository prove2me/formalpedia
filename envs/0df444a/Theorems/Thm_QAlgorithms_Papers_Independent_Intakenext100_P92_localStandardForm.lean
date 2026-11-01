-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_localStandardForm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.localStandardForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:36:49.065181+00:00
-- url     : https://prove2.me/theorems/646ed860-09bf-47e4-b1d2-181713e39052
-- title:
--   Local symplectic standard form of physical covariances
-- statement:
--   Let $\rho$ be a normalized density of two complete oscillators, with finite first and second moments and covariance $V$ in the order $(q_1,p_1,q_2,p_2)$, using $\hbar=1$ and half-anticommutators. There exist real $a,b,c_1,c_2$ and real local symplectic matrices $S_1,S_2$, satisfying $S_jJS_j^T=J$ for $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, such that
--
--   $$
--   (S_1\oplus S_2)V(S_1\oplus S_2)^T=
--   \begin{pmatrix}a&0&c_1&0\\0&a&0&c_2\\c_1&0&b&0\\0&c_2&0&b\end{pmatrix}.
--   $$
--
--   The two correlation parameters are independent. This is a local block normal form for an actual physical covariance, rather than a diagonalization by a general global symplectic matrix.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, PDF p.4, argument after (18): local symplectic standard form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P92

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel unitaryCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, argument after (18): actual finite covariances admit the local
block standard form, with two independent correlation entries. -/
theorem localStandardForm (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (hmom : TwoModeMoments rho d V) :
    ∃ (S1 S2 : LocalMatrix) (a b c1 c2 : ℝ),
      LocalSymplectic S1 ∧ LocalSymplectic S2 ∧
        localCovarianceAction V S1 S2 = twoModeStandard a b c1 c2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
