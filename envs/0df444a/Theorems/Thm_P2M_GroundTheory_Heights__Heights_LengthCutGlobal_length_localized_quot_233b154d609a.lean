-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:48.768874+00:00
-- url     : https://prove2.me/theorems/c52b8817-a15f-5131-9644-10112374a77a
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global length localized quot 233b154d609a: P2 M Ground Theory Heights  Heights Length Cut Global length localized quot 233b154d609a
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global length localized quot 233b154d609a construction uses the P2 M Ground Theory Heights  Heights Length Cut Global length localized quot 233b154d609a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L99-L111

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

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (C ⧸ P)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«length_localized_quot» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a
