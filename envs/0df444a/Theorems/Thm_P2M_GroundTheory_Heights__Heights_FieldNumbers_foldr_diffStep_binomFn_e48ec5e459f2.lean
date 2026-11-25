-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_binomFn_e48ec5e459f2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_binomFn_e48ec5e459f2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:43.877056+00:00
-- url     : https://prove2.me/theorems/35662d4a-a58e-54fb-a3ce-8fb7e645fbd6
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step binom Fn e48ec5e459f2: P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step binom Fn e48ec5e459f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step binom Fn e48ec5e459f2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step binom Fn e48ec5e459f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L94-L103

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_binomFn_e48ec5e459f2 (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«foldr_diffStep_binomFn» := P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_binomFn_e48ec5e459f2
