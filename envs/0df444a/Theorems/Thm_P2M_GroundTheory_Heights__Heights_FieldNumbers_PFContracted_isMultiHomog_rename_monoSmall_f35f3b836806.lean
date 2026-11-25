-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomog_rename_monoSmall_f35f3b836806
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomog_rename_monoSmall_f35f3b836806
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:58.766351+00:00
-- url     : https://prove2.me/theorems/adcf0d4c-cf09-4930-bb31-1c16f72f737c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog rename mono Small f35f3b836806: P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog rename mono
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog rename mono Small f35f3b836806 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog rename mono Small f35f3b836806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L256-L263

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
variable {F K K' j ι'}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomog_rename_monoSmall_f35f3b836806 (i : ∀ k', ι' k') (e : K → ℕ) :
    IsMultiHomog (rename (blockIncl j ι') (monoSmall (F := F) i e)) (pullNat K K' j e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«isMultiHomog_rename_monoSmall» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomog_rename_monoSmall_f35f3b836806
