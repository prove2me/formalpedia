-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:28.89654+00:00
-- url     : https://prove2.me/theorems/01e2a057-077d-56ec-91b4-92622dd3ecd7
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block map split Equiv a10732f4e974: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block map split Equiv a10732f4e974
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block map split Equiv a10732f4e974 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block map split Equiv a10732f4e974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L92-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974 (I : Ideal (MRing ι F)) :
    (addBlockPrime N I).map (splitEquiv F ι N) = I.map C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«map_splitEquiv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_map_splitEquiv_a10732f4e974
