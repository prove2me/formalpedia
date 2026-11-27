-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_field_of_isIntegral_image__4fafb0d6e24d
-- name    : P2M_GlobalTheory_T_exists_field_of_isIntegral_image__4fafb0d6e24d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:12:16.248799+00:00
-- url     : https://prove2.me/theorems/95dacaa5-e028-4d14-a835-98ec538a9b50
-- title:
--   P2 M Global Theory T exists field of is Integral image  4fafb0d6e24d: P2 M Global Theory T exists field of is Integral image  4fafb0d6e24d
-- statement:
--   The P2 M Global Theory T exists field of is Integral image  4fafb0d6e24d construction uses the P2 M Global Theory T exists field of is Integral image  4fafb0d6e24d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfIsIntegralImageStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfIsIntegralImageStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfIsIntegralImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfIsIntegralImageStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_field_of_isIntegral_image__4fafb0d6e24d : ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by sorry

alias «GlobalTheory».«T».«exists_field_of_isIntegral_image'» := P2M_GlobalTheory_T_exists_field_of_isIntegral_image__4fafb0d6e24d
