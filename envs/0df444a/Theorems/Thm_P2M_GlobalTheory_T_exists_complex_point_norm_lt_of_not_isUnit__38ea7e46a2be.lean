-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_complex_point_norm_lt_of_not_isUnit__38ea7e46a2be
-- name    : P2M_GlobalTheory_T_exists_complex_point_norm_lt_of_not_isUnit__38ea7e46a2be
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:52.886573+00:00
-- url     : https://prove2.me/theorems/68f96857-1a48-436e-9956-dad6958d4da1
-- title:
--   P2 M Global Theory T exists complex point norm lt of not is Unit  38ea7e46a2be: P2 M Global Theory T exists complex point norm lt of not is Unit  38ea7e46a2be
-- statement:
--   The P2 M Global Theory T exists complex point norm lt of not is Unit  38ea7e46a2be construction uses the P2 M Global Theory T exists complex point norm lt of not is Unit  38ea7e46a2be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnitStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnitStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_complex_point_norm_lt_of_not_isUnit__38ea7e46a2be : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧ ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by sorry

alias «GlobalTheory».«T».«exists_complex_point_norm_lt_of_not_isUnit'» := P2M_GlobalTheory_T_exists_complex_point_norm_lt_of_not_isUnit__38ea7e46a2be
