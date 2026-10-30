-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_anisotropic_de_bruijn
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.anisotropic_de_bruijn
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:09:13.162792+00:00
-- url     : https://prove2.me/theorems/ad6a2b53-068e-44cf-a17e-de66cbd90996
-- title:
--   Section III B, Eq.(21): anisotropic quantum de Bruijn identity
-- statement:
--   Let $n\ge1$, let $\rho$ be a normalized full $n$-mode density of finite mean photon number, let $\gamma$ be positive definite or zero, and let $t>0$. Suppose the displacement relative entropy of $H_\gamma(t)\rho$ is finite near zero and twice Frechet differentiable there in the explicit derivative domain. Denote its full Hessian by $J$. The evolved entropy is finite and differentiable at $t$, with
--
--   $$\frac{d}{dt}S(H_\gamma(t)\rho)=\frac14\operatorname{tr}(J\gamma).$$
--
--   This is the anisotropic matrix de Bruijn identity, expressed without an unbounded logarithmic commutator or a default derivative.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III B, Eq.(21): anisotropic quantum de Bruijn identity

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

/-- PDF p.4, Section III B, (21): anisotropic de Bruijn identity at positive
smoothing times, with a finite genuine displacement Hessian. Finite entropy,
entropy differentiability and its value are conclusions, not hypotheses. -/
theorem anisotropic_de_bruijn {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients)
    (gamma : Cov n) (hGamma : gamma = 0 ∨ gamma.PosDef) (t : ℝ) (ht : 0 < t)
    (hFisher : MatrixFisherRegular (anisotropicHeat gamma t rho.coefficients)) :
    extendedEntropyNats (anisotropicHeat gamma t rho.coefficients) ≠ ⊤ ∧
    HasDerivAt (fun s : ℝ =>
      (extendedEntropyNats (anisotropicHeat gamma s rho.coefficients)).toReal)
      ((matrixFisher (anisotropicHeat gamma t rho.coefficients) * gamma).trace / 4) t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
