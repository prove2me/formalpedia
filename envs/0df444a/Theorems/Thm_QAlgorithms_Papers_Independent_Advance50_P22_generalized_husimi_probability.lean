-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_generalized_husimi_probability
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.generalized_husimi_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:12:05.15483+00:00
-- url     : https://prove2.me/theorems/b0521135-4605-47ff-a2db-c82daff0d7a5
-- title:
--   Section III C.1, Eq.(30): generalized Husimi probability density
-- statement:
--   Let $n\ge1$, let $\rho$ be any normalized full $n$-mode density, and let $\Gamma$ be a real physical covariance in the vacuum-$I$ convention. Let $\rho_{x,\Gamma}$ be the Gaussian density with mean $x$ and covariance $\Gamma$. Then
--
--   $$Q_\Gamma(x)=\frac{\operatorname{Tr}(\rho\rho_{x,\Gamma})}{(2\pi)^n}=\int_{\mathbb R^{2n}}e^{-k^T\Gamma k/4-ik^Tx}\chi_\rho(k)\,\frac{dk}{(2\pi)^{2n}}.$$
--
--   The function $Q_\Gamma$ is continuous, nonnegative and integrable, and $\int Q_\Gamma(x)\,dx=1$. This supplies a genuine classical probability density without interpreting the formal negative-covariance kernel as a quantum state.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 5, Section III C.1, Eq.(30): generalized Husimi probability density

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF p.5, Section III C.1, (30): generalized Husimi probability density.
The Fourier denominator is (2*pi)^(2n), unlike the overlap denominator (2*pi)^n.
No negative-covariance 'state' from the formal inversion (31) is introduced. -/
theorem generalized_husimi_probability {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (Gamma : Cov n) (hGamma : PhysicalCovariance Gamma) :
    Continuous (generalizedHusimi Gamma rho.coefficients) ∧
    (∀ x : InterleavedCoordinateVector n, 0 ≤ generalizedHusimi Gamma rho.coefficients x) ∧
    Integrable (generalizedHusimi Gamma rho.coefficients) ∧
    (∫ x : InterleavedCoordinateVector n, generalizedHusimi Gamma rho.coefficients x) = 1 ∧
    (∀ x : InterleavedCoordinateVector n, generalizedHusimi Gamma rho.coefficients x =
      ((2 * Real.pi) ^ (2 * n))⁻¹ *
        (∫ k : InterleavedCoordinateVector n, Complex.exp
          (((-(∑ i, ∑ j, k i * Gamma i j * k j) / 4 : ℝ) : ℂ) -
            Complex.I * ((∑ i, k i * x i : ℝ) : ℂ)) *
          multimodeWeylTrace rho.coefficients k).re) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
