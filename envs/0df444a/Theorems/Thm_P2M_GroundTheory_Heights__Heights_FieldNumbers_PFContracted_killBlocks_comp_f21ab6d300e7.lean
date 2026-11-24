-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:14.666659+00:00
-- url     : https://prove2.me/theorems/6fea9740-f4bf-41be-acc2-b8b3cdca14aa
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks comp f21ab6d300e7: P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks comp f21ab6d300e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks comp f21ab6d300e7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks comp f21ab6d300e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L50-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7 {T T' : Finset K} (h : T ⊆ T') :
    (killBlocks (ι := ι) (F := F) T').comp (killBlocks T) = killBlocks T' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«killBlocks_comp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7
