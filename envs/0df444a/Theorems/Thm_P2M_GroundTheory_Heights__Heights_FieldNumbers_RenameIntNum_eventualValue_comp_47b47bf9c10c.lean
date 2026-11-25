-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:24.816179+00:00
-- url     : https://prove2.me/theorems/3266782e-4894-4c9c-a525-cb46a284a403
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num eventual Value comp 47b47bf9c10c: P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num eventual Value comp 47b47bf9c10c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num eventual Value comp 47b47bf9c10c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num eventual Value comp 47b47bf9c10c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L30-L46

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«RenameIntNum».«eventualValue_comp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c
