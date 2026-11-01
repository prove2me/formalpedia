-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_quantumAuxiliaryLowerBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.quantumAuxiliaryLowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:17:12.85739+00:00
-- url     : https://prove2.me/theorems/d034509a-4238-47a3-9255-af88d2f50681
-- title:
--   Unnumbered result: quantum-auxiliary single-letter lower bound
-- statement:
--   For a valid finite nonempty classical–quantum source, nonnegative finite distortion d(x,z), and target D>=0, let R_B(D) be the infimum of rates achievable by deterministic finite-block encoders and message-controlled reconstruction POVMs, using every positive rate slack and all sufficiently large positive blocklengths with expected distortion at most D. For every positive finite dimension of C, choose density matrices tau_x and an arbitrary joint CB reconstruction POVM. Compute the distortion on sum_x p(x)|x><x| tensor tau_x tensor rho_x and the bit-valued objective I(X;C)-I(C;B). The minimum R_B^*(D) of this objective over the entire feasible domain obeys R_B^*(D)<=R_B(D). Whenever finite, the minimum is attained by some such finite-dimensional datum. Empty feasible sets have value +infinity. No dimension bound, achievability claim, or equality with the operational rate is asserted.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 17, Unnumbered result: quantum-auxiliary single-letter lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.17, unnumbered quantum-auxiliary lower bound: the printed minimum
is a lower bound on the operational R_B(d). All positive finite C dimensions
are allowed and the finite minimum is ATTAINED, asserted rather than assumed.
The literal p.16 rate definition is sufficient for this converse despite the
separate zero-distortion defect of Theorem 4.2. Empty feasible sets have value infinity. -/
theorem quantumAuxiliaryLowerBound {X B : Type} [Fintype X] [Fintype B]
    [Nonempty X] [Nonempty B] (E : CQData X B) (hE : E.Valid)
    (d : X → X → ℝ) (hd : ∀ x z, 0 ≤ d x z) (D : ℝ) (hD : 0 ≤ D) :
    quantumRDValue E d D ≤ exactDistortionRate E d D ∧
    (quantumRDValue E d D ≠ ⊤ →
      ∃ P : QuantumRDChoice X B, quantumRDExpected E d P ≤ D ∧
        ENNReal.ofReal (quantumRDCost E P) = quantumRDValue E d D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
