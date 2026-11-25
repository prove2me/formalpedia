-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:42.668359+00:00
-- url     : https://prove2.me/theorems/9654f1c8-e661-5b53-8c07-b458dcf625f3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers div Cycle support finite 8449e904c3ec: P2 M Ground Theory Heights  Heights Field Numbers div Cycle support finite 8449e904c3ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers div Cycle support finite 8449e904c3ec construction uses the P2 M Ground Theory Heights  Heights Field Numbers div Cycle support finite 8449e904c3ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRational.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRational.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (f : MRing ι F) :
    (Function.support (divCycle P f)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«divCycle_support_finite» := P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec
