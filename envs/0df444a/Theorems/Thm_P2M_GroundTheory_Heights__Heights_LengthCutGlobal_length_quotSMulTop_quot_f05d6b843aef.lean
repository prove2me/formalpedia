-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:01.084921+00:00
-- url     : https://prove2.me/theorems/3ced895e-197a-4ec2-8974-23069f7fe8b5
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top quot f05d6b843aef: P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top quot f05d6b843aef
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top quot f05d6b843aef construction uses the P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top quot f05d6b843aef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L71-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L71-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
omit [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef {y : C} (hmax : (P ⊔ Ideal.span {y}).IsMaximal) :
    Module.length C (QuotSMulTop y (C ⧸ P)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«length_quotSMulTop_quot» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef
