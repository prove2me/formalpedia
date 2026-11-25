-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:36.768593+00:00
-- url     : https://prove2.me/theorems/6df6c40a-98d7-4381-ad39-f5c018b7d0b2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers extend equiv zero fbc06038a4c0: P2 M Ground Theory Heights  Heights Field Numbers extend equiv zero fbc06038a4c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers extend equiv zero fbc06038a4c0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers extend equiv zero fbc06038a4c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L56-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0 {A B : Type} (E : A ≃ B) (d : A → ℕ) :
    Function.extend E d 0 = d ∘ E.symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«extend_equiv_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0
