-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:19.852653+00:00
-- url     : https://prove2.me/theorems/545261ac-d82c-4363-bdad-7a678d5a4ef3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers foldr new Block ce47eadd08da: P2 M Ground Theory Heights  Heights Field Numbers foldr new Block ce47eadd08da
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers foldr new Block ce47eadd08da construction uses the P2 M Ground Theory Heights  Heights Field Numbers foldr new Block ce47eadd08da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L68-L75

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da (j : ℕ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (List.replicate j (newBlockDeg : Option K → ℤ)).foldr diffStep (prodFn A B) =
      prodFn A (diff1^[j] B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«foldr_newBlock» := P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da
