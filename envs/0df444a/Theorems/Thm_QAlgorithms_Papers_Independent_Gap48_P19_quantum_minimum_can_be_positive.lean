-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_quantum_minimum_can_be_positive
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.quantum_minimum_can_be_positive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:10:09.921234+00:00
-- url     : https://prove2.me/theorems/a4e19c56-c7ef-4857-858a-15566473ae8b
-- title:
--   The unrestricted quantum minimum can be positive
-- statement:
--   There exists a density matrix $\rho_{AB}$ on two two-dimensional complex Hilbert spaces and a real number $m>0$ such that, for all finite-dimensional density extensions with fixed marginal $\rho_{AB}$,
--
--   $$\min_{\omega:\,\operatorname{Tr}_L\omega=\rho_{AB}}I_\omega(A:B\mid L)=m>0.$$
--
--   The auxiliary dimension ranges over all positive finite integers, and this particular minimum is attained. Entropies are in nats. This is an existential contrast with the classical zero minimum; it asserts no general attainment or characterization for arbitrary entangled states.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 4, §2, paragraph after Eq.(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, after (8): the unrestricted quantum minimum can be positive.
This is existential, not a claim about every entangled state. Uses corrected (4). -/
theorem quantum_minimum_can_be_positive :
    ∃ rho : Mat (Bool × Bool), IsDensityMatrix rho ∧
      ∃ m : ℝ, 0 < m ∧ IsLeast (quantumScores rho) m := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
