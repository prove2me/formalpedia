-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:58.242489+00:00
-- url     : https://prove2.me/theorems/dd0ad10c-0b3d-4dbe-80fc-80f27b789a47
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rename split Var symm aa89fdc4ec16: P2 M Ground Theory Heights  Heights Field Numbers rename split Var symm aa89fdc4ec16
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rename split Var symm aa89fdc4ec16 construction uses the P2 M Ground Theory Heights  Heights Field Numbers rename split Var symm aa89fdc4ec16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L51-L54

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16 {R : Type*} [CommSemiring R] (f : MvPolynomial (Σ k', ι' k') R) :
    rename (splitVar j ι') (rename (splitVarEquiv j ι').symm f) = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«rename_splitVar_symm» := P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16
