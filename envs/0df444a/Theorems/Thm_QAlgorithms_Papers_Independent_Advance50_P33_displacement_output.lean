-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_displacement_output
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.displacement_output
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:31:45.815505+00:00
-- url     : https://prove2.me/theorems/7a35a422-85e1-45c8-abe4-c2039485ccca
-- title:
--   A proof displacement shifts both unveiling outputs
-- statement:
--   Use the full oscillator space, normalized coherent states, and $\hbar=1$, so $D(it/\sqrt2)$ shifts the physical momentum quadrature by $t$. Let $a\ne0$, $A=\sqrt2a$, and $b\in\{0,1\}$. Fix the ideal balanced beam splitter $B$ by the amplitude action $(z,w)\mapsto((z-w)/\sqrt2,(z+w)/\sqrt2)$. If Alice displaces only the proof of the honest encoding by $\sqrt2d$, with $d\in\mathbb R$, then
--   $$
--   B(I\otimes D(id))|\chi_b(a)\rangle=
--   D(-id/\sqrt2)|c_b(A)\rangle\otimes|id/\sqrt2\rangle.
--   $$
--   The displayed vector has norm one. Thus the checked cat output shifts by $-d$ and the other output shifts by $+d$. This identity describes the specified displacement strategy independently of the paper's separate global Gaussian-optimality assertion.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 5, III.B–C: action of a proof displacement on both unveiling outputs

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--6: exact action of the proof shift sqrt(2)*d on BOTH unveiling
outputs. hbar=1: proof D(i*d), cat D(-i*d/sqrt(2)), other output D(i*d/sqrt(2)).
The interferometer includes losslessness and the matched optical phase convention. -/
theorem displacement_output :
    CoherentRealized ∧ DisplacementRealized ∧ IsBalanced balancedInterferometer ∧
    ∀ (a : ℂ), a ≠ 0 → ∀ (b : Bool) (d : ℝ),
      ‖displacedOutput ((Real.sqrt 2 : ℂ) * a) b d‖ = 1 ∧
      balancedInterferometer (attackedChi a b (pShift (Real.sqrt 2 * d))) =
        displacedOutput ((Real.sqrt 2 : ℂ) * a) b d := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
