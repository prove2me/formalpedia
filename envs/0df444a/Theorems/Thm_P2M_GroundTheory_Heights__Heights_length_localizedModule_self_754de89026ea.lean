-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea
-- name    : P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:56.934809+00:00
-- url     : https://prove2.me/theorems/8714e5d3-8af9-4418-a2df-2d6570ae5268
-- title:
--   P2 M Ground Theory Heights  Heights length localized Module self 754de89026ea: P2 M Ground Theory Heights  Heights length localized Module self 754de89026ea
-- statement:
--   The P2 M Ground Theory Heights  Heights length localized Module self 754de89026ea construction uses the P2 M Ground Theory Heights  Heights length localized Module self 754de89026ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedQuotient.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedQuotient.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedQuotient
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
universe u

theorem P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_localizedModule_self» := P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea
