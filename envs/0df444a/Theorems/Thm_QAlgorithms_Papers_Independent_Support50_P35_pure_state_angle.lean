-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_pure_state_angle
-- name    : QAlgorithms.Papers.Independent.Support50.P35.pure_state_angle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:43:56.257708+00:00
-- url     : https://prove2.me/theorems/c7247052-ccd3-4373-86e7-22565169e76c
-- title:
--   Pure-coordinate angles and attained maximal separation
-- statement:
--   Let \(D\geq2\), and let \(r,s\) represent normalized pure states \(\rho=(I+r\cdot\lambda)/D\) and \(\sigma=(I+s\cdot\lambda)/D\). With \(\theta\) their ordinary Euclidean coordinate angle,
--
--   $$
--   \operatorname{tr}(\rho\sigma)=\frac1D+\frac{r\cdot s}{D^2},\qquad
--   \theta=\arccos\frac{D\operatorname{tr}(\rho\sigma)-1}{D-1}
--   \leq\arccos\frac1{1-D}.
--   $$
--
--   There exist pure coordinate vectors attaining the displayed upper bound. For every pure coordinate vector \(r\), its antipode \(-r\) is pure if and only if \(D=2\). The restriction \(D\geq2\) makes both vectors nonzero and all angle denominators meaningful. This quantifies the maximal separation inside the pure-state subset of the coordinate sphere.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 14, Unnumbered Eqs.(40)–(41): pure-state angle and maximal separation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.14, Eqs.(40)--(41): angle, attained maximal separation, and the
antipode restriction. D>=2 excludes zero vectors and zero denominator. -/
theorem pure_state_angle (D : ℕ) (hD : 2 ≤ D) :
    (∀ r s : TracelessIndex D → ℝ, r ∈ pureQuadraticSet D → s ∈ pureQuadraticSet D →
      (scaledGellmannState r * scaledGellmannState s).trace.re = 1 / (D : ℝ) + dotProduct r s / (D : ℝ) ^ 2 ∧
      coordinateAngle r s = Real.arccos
        (((D : ℝ) * (scaledGellmannState r * scaledGellmannState s).trace.re - 1) / ((D : ℝ) - 1)) ∧
      coordinateAngle r s ≤ Real.arccos (1 / (1 - (D : ℝ)))) ∧
    (∃ r s : TracelessIndex D → ℝ, r ∈ pureQuadraticSet D ∧ s ∈ pureQuadraticSet D ∧
      coordinateAngle r s = Real.arccos (1 / (1 - (D : ℝ)))) ∧
    (∀ r : TracelessIndex D → ℝ, r ∈ pureQuadraticSet D →
      (-r ∈ pureQuadraticSet D ↔ D = 2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
