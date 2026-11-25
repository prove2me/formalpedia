-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_resDeg_point_7c1566581954
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_resDeg_point_7c1566581954
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:20.72928+00:00
-- url     : https://prove2.me/theorems/829e61a2-e3d4-513b-81a3-e864b6a73d2f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers res Deg point 7c1566581954: P2 M Ground Theory Heights  Heights Field Numbers res Deg point 7c1566581954
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers res Deg point 7c1566581954 construction uses the P2 M Ground Theory Heights  Heights Field Numbers res Deg point 7c1566581954 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L278-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L278-L310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_resDeg_point_7c1566581954 (F : Type*) [Field F] : resDeg (⊥ : Ideal (MRing (ProjIdx 0) F)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«resDeg_point» := P2M_GroundTheory_Heights__Heights_FieldNumbers_resDeg_point_7c1566581954
