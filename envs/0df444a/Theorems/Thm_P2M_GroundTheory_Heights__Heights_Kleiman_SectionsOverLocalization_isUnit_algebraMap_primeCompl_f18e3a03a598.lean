-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_isUnit_algebraMap_primeCompl_f18e3a03a598
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_isUnit_algebraMap_primeCompl_f18e3a03a598
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:15.310631+00:00
-- url     : https://prove2.me/theorems/5f74d102-f0fd-4e49-827a-0a2b5604ede8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization is Unit algebra Map prime Compl f18e3a03a598: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization is Unit alge
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization is Unit algebra Map prime Compl f18e3a03a598 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization is Unit algebra Map prime Compl f18e3a03a598 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefGenericLocalize.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefGenericLocalize.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefGenericLocalizeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeNefAboveSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefGenericLocalize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_isUnit_algebraMap_primeCompl_f18e3a03a598 {S : Type} [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] {K : Type} [Field K]
    [Algebra S K] (h : Function.Injective (algebraMap S K)) (y : 𝔪.primeCompl) : IsUnit (algebraMap S K y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«isUnit_algebraMap_primeCompl» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_isUnit_algebraMap_primeCompl_f18e3a03a598
