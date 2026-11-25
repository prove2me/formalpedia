-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_lt_withBotWithTop_6ec59031adae
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_lt_withBotWithTop_6ec59031adae
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:06.592798+00:00
-- url     : https://prove2.me/theorems/c6cc3507-7a9b-5955-a81a-8fa261ed66b2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast lt with Bot With Top 6ec59031adae: P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast lt with Bot With Top
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast lt with Bot With Top 6ec59031adae construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast lt with Bot With Top 6ec59031adae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/BlockInclInjectiveOfEmbedding.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/BlockInclInjectiveOfEmbedding.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_lt_withBotWithTop_6ec59031adae {a b : ℕ} (h : a < b) :
    ((a : ℕ) : WithBot (WithTop ℤ)) < ((b : ℕ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«natCast_lt_withBotWithTop» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_lt_withBotWithTop_6ec59031adae
