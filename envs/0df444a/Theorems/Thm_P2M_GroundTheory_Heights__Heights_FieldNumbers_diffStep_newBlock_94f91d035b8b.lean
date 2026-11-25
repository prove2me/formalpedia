-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:16.097041+00:00
-- url     : https://prove2.me/theorems/2d6a33f0-12d2-420c-80ea-07bc0d3a8a70
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers diff Step new Block 94f91d035b8b: P2 M Ground Theory Heights  Heights Field Numbers diff Step new Block 94f91d035b8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers diff Step new Block 94f91d035b8b construction uses the P2 M Ground Theory Heights  Heights Field Numbers diff Step new Block 94f91d035b8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L49-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
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
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (newBlockDeg : Option K → ℤ) (prodFn A B) = prodFn A (diff1 B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«diffStep_newBlock» := P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b
