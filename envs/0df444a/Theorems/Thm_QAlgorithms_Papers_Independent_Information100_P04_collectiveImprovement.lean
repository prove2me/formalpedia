-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_collectiveImprovement
-- name    : QAlgorithms.Papers.Independent.Information100.P04.collectiveImprovement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:34:15.357978+00:00
-- url     : https://prove2.me/theorems/b919b8c1-d547-4197-9305-a74bf52701c5
-- title:
--   Rational 24-copy effect improving the achievable quadratic coefficient
-- statement:
--   There exists an effect $E$ on 24 qutrit pairs whose complex matrix entries have rational real and imaginary parts, such that $0\le E\le I$ and $0\le E^\Gamma\le(2/5)I$. Its polynomial acceptance $a(p)=\operatorname{Tr}(\rho_p^{\otimes24}E)$ satisfies $a(1/2)=2/5$ and $a'(1/2)=s$, where $s=4118621179428546867727313/1283031261738279119093760$. Define $g(p)=D_{\rm bin}(a(p)\|2/5)/24$ when $a(p)>2/5$, and zero otherwise. Then $g(p)\le E_{d,\mathrm{PPT}}(\rho_p)$ for $p\in[1/2,1]$, and
--
--   $$g(1/2+\delta)=\kappa_{24}\delta^2+O(\delta^3),\qquad\kappa_{24}=\frac{s^2}{48(2/5)(3/5)\ln2}>\frac2{3\ln2}.$$
--
--   The expansion is from the right, with one constant and one positive neighborhood independent of $\delta$. On a sufficiently small right neighborhood, $g$ is strictly larger than the one-copy curve in (121) at $d=3$. This certifies an improvement of a fixed achievable curve, without claiming an expansion of the unknown operational rate.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 29, eq131-132

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eqs.(131)–(132), PDF p.29: existence of the rational 24-copy certificate, its exact
slope, and an expansion of its achievable curve, not of the unknown operational rate. -/
theorem collectiveImprovement :
    ∃ E : Matrix ((Fin 24 → Fin 3) × (Fin 24 → Fin 3))
      ((Fin 24 → Fin 3) × (Fin 24 → Fin 3)) ℂ,
      IsRationalMatrix E ∧ IsEffect E ∧ (gamma E).PosSemidef ∧
      ((2/5:ℂ) • 1 - gamma E).PosSemidef ∧
      collectiveAcceptance E (1/2) = 2/5 ∧
      HasDerivAt (collectiveAcceptance E) collectiveSlope (1/2) ∧
      (∀ p : ℝ, 1/2 ≤ p → p ≤ 1 → collectiveCurve E p ≤ distillable (werner 3 p)) ∧
      collectiveCoefficient > 2/(3*Real.log 2) ∧
      (∃ C > (0:ℝ), ∃ eps > (0:ℝ), ∀ delta : ℝ, 0 < delta → delta < eps →
        |collectiveCurve E (1/2+delta)-collectiveCoefficient*delta^2| ≤ C*delta^3) ∧
      (∃ eps > (0:ℝ), ∀ delta : ℝ, 0 < delta → delta < eps →
        binaryD ((2+2*(1/2+delta))/4) (3/4) < collectiveCurve E (1/2+delta)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
