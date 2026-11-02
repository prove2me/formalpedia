-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_ideal_spectral_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.ideal_spectral_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:55:13.788486+00:00
-- url     : https://prove2.me/theorems/f1d4c0ad-6486-4ca3-b4a4-051d0d248d8a
-- title:
--   §III B, Eq.(27), Appendix B1: spectral error bound
-- statement:
--   Let normalized pure samples, $K\ge2$, generate all operators on their span, of dimension $d$, and fix an anchor. Let $\lambda_\perp$ be the norm of the vectorized compressed reflection channel. Then $0\le\lambda_\perp<1$. For every supported input density operator, every ambient target unitary, and every integer $T\ge1$, the ideal averaged emulator obeys
--
--   $$F(\mathcal E_U(\rho),U\rho U^\dagger)\ge1-\sqrt{d-1}\,\lambda_\perp^T.$$
--
--   If $d\ge2$, $0<\epsilon_{\rm id}<1$, and $T\ge1$ satisfies
--
--   $$T\ge\frac{\log(2\epsilon_{\rm id}^{-2}(d-1))}{1-\lambda_\perp},$$
--
--   then its trace distance from the target is at most $\epsilon_{\rm id}$. At $d=1$ the zero-round anchor preparation is already exact for supported inputs. The formula avoids $\log\lambda_\perp$ and remains meaningful when $\lambda_\perp=0$. This separates ideal convergence from sample-based reflection errors.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 7, §III B, Eq.(27), Appendix B1: spectral error bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.7,17–18, Eq.(27)/B18: the spectral gap is a conclusion, not a premise.
B12 has sqrt(d-1); B14 is its weaker d>=2 corollary. T>=1 handles lambda=0, and
rank one is separated from the logarithm. -/
theorem ideal_spectral_error (phi : K → EuclideanSpace ℂ I) (a : K)
    (hK : 2 ≤ Fintype.card K) (hphi : ∀ k, IsState (phi k))
    (hgen : Generates (pureSamples phi)) :
    0 ≤ lambdaPerp phi a ∧ lambdaPerp phi a < 1 ∧
    (∀ (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ), IsDensityMatrix rho →
      InSampleSupport (pureSamples phi) rho → ∀ T : ℕ, 1 ≤ T →
      1 - Real.sqrt (sampleDimension (pureSamples phi) - 1 : ℝ) * lambdaPerp phi a ^ T ≤
        rootFidelity (emulate phi a (U : Matrix I I ℂ) T rho) (densityConjugation (U : Matrix I I ℂ) rho)) ∧
    (∀ (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ), IsDensityMatrix rho →
      InSampleSupport (pureSamples phi) rho → ∀ eps : ℝ, 0 < eps → eps < 1 →
      2 ≤ sampleDimension (pureSamples phi) → ∀ T : ℕ, 1 ≤ T →
      Real.log (2 * eps⁻¹ ^ 2 * (sampleDimension (pureSamples phi) - 1 : ℝ)) /
        (1 - lambdaPerp phi a) ≤ T →
      traceDistance (emulate phi a (U : Matrix I I ℂ) T rho) (densityConjugation (U : Matrix I I ℂ) rho) ≤ eps) ∧
    (sampleDimension (pureSamples phi) = 1 →
      ∀ (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ), IsDensityMatrix rho →
        InSampleSupport (pureSamples phi) rho → emulate phi a (U : Matrix I I ℂ) 0 rho = densityConjugation (U : Matrix I I ℂ) rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
