-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:07.693444+00:00
-- url     : https://prove2.me/theorems/18e7121d-64d8-58f6-9a16-e54e30d38f55
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks of is Multi Homog d5143d61805c: P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks of is Multi Homog
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks of is Multi Homog d5143d61805c construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks of is Multi Homog d5143d61805c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L100-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L100-L119

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c (T : Finset K) {p : MRing ι F} {b : K → ℕ}
    (hp : IsMultiHomog p b) : killBlocks T p = if ∀ k ∈ T, b k = 0 then p else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«killBlocks_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c
