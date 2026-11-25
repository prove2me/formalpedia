-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:13.72951+00:00
-- url     : https://prove2.me/theorems/b82980a2-ddaa-5345-bf7f-5a3421c58526
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Relevant map c55c7df7a8e9: P2 M Ground Theory Heights  Heights Field Numbers is Relevant map c55c7df7a8e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Relevant map c55c7df7a8e9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Relevant map c55c7df7a8e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L143-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
variable {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9 {I : Ideal (MRing ι F)} (hI : IsRelevant I) :
    IsRelevant (I.map (map (algebraMap F F'))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isRelevant_map» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9
