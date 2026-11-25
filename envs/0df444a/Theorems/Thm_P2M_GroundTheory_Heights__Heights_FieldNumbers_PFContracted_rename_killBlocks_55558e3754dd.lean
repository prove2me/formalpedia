-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:03.753449+00:00
-- url     : https://prove2.me/theorems/bb702a20-2dd3-4435-a032-e77f285d0011
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename kill Blocks 55558e3754dd: P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename kill Blocks 55558e3754dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename kill Blocks 55558e3754dd construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename kill Blocks 55558e3754dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L177-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L177-L186

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
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd (j : K ↪ K') (ι' : K' → Type*) (T : Finset K)
    (q : MRing (fun k => ι' (j k)) F) :
    rename (blockIncl j ι') (killBlocks T q) = killBlocks (T.map j) (rename (blockIncl j ι') q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«rename_killBlocks» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd
