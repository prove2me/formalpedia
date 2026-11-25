-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:48.682598+00:00
-- url     : https://prove2.me/theorems/c4ca317d-9496-4d5e-ab3a-ebe44e21c4cc
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num mixed Diff comp cdf665d4760a: P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num mixed Diff comp cdf665d4760a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num mixed Diff comp cdf665d4760a construction uses the P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num mixed Diff comp cdf665d4760a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L48-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«RenameIntNum».«mixedDiff_comp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a
