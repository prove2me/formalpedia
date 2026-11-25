-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d
-- name    : P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:41.974934+00:00
-- url     : https://prove2.me/theorems/aea6aa1b-4caf-4acf-9c52-f7733fb16110
-- title:
--   P2 M Global Theory Nef Place Residue Power Bound pow le one iff  b5da8e0cef6d: P2 M Global Theory Nef Place Residue Power Bound pow le one iff  b5da8e0cef6d
-- statement:
--   The P2 M Global Theory Nef Place Residue Power Bound pow le one iff  b5da8e0cef6d construction uses the P2 M Global Theory Nef Place Residue Power Bound pow le one iff  b5da8e0cef6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceRestrictionExistsPow.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceRestrictionExistsPow.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]

theorem P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by sorry

alias «GlobalTheory».«Nef».«PlaceResiduePowerBound».«pow_le_one_iff'» := P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d
