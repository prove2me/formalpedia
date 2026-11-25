-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_binomFn_sub_b7addd9f464d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_binomFn_sub_b7addd9f464d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:05.452253+00:00
-- url     : https://prove2.me/theorems/0340b33d-e0a5-4686-9667-a8b866caaae1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers binom Fn sub b7addd9f464d: P2 M Ground Theory Heights  Heights Field Numbers binom Fn sub b7addd9f464d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers binom Fn sub b7addd9f464d construction uses the P2 M Ground Theory Heights  Heights Field Numbers binom Fn sub b7addd9f464d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L33-L48

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_binomFn_sub_b7addd9f464d (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«binomFn_sub» := P2M_GroundTheory_Heights__Heights_FieldNumbers_binomFn_sub_b7addd9f464d
