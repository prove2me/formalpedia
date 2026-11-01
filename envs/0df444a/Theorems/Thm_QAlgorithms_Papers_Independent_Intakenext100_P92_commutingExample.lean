-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_commutingExample
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.commutingExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:34:17.235294+00:00
-- url     : https://prove2.me/theorems/8d29cb39-7fe5-4417-96a2-a276d870966b
-- title:
--   Commuting nonlocal quadratures obey a separable variance bound
-- statement:
--   For two canonical oscillators with $[q_j,p_k]=i\delta_{jk}$, put $X=q_1+p_1+q_2+p_2$ and $Y=q_1-p_1-q_2+p_2$. For every normalized separable density $\rho$ with finite first and second moments,
--
--   $$
--   [X,Y]\psi=0\quad\text{for every finite-particle vector }\psi,\qquad
--   \operatorname{Var}_\rho(X)+\operatorname{Var}_\rho(Y)\ge4.
--   $$
--
--   The variances are the quadratic forms of the actual half-anticommutator covariance of $\rho$, not standard deviations. This example shows that separability constrains even commuting nonlocal observables.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 3, PDF p.3: commuting nonlocal observables have separable variance sum at least four

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

/-- PDF p.3 example following (11): the commutator is zero on the common
finite-particle core, but separable states have variance sum at least four.
The source's x_j denotes its previously introduced q_j. -/
theorem commutingExample (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (hmom : TwoModeMoments rho d V) (hsep : IsSeparable rho) :
    (∀ psi : (ℕ × ℕ) →₀ ℂ,
      linearAction exampleX (linearAction exampleY psi) -
        linearAction exampleY (linearAction exampleX psi) = 0) ∧
    4 ≤ quadratureVariance V exampleX + quadratureVariance V exampleY := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
