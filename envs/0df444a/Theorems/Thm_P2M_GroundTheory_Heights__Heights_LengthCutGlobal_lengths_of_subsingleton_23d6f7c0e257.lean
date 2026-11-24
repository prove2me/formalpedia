-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:08.843749+00:00
-- url     : https://prove2.me/theorems/b3395980-08d7-4fae-bbdd-47ec2013a5dc
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global lengths of subsingleton 23d6f7c0e257: P2 M Ground Theory Heights  Heights Length Cut Global lengths of subsingleton 23d6f7c0e257
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global lengths of subsingleton 23d6f7c0e257 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global lengths of subsingleton 23d6f7c0e257 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L56-L60

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

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257 (y : C) (X : Type*) [AddCommGroup X] [Module C X] [Subsingleton X] :
    Module.length C (QuotSMulTop y X) = 0 ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«lengths_of_subsingleton» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
