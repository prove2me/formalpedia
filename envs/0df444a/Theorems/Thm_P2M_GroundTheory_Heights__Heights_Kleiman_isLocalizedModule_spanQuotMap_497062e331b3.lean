-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:01.437545+00:00
-- url     : https://prove2.me/theorems/44aab757-2b16-41c3-8240-fe5d070102bc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Localized Module span Quot Map 497062e331b3: P2 M Ground Theory Heights  Heights Kleiman is Localized Module span Quot Map 497062e331b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Localized Module span Quot Map 497062e331b3 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Localized Module span Quot Map 497062e331b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L55-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L55-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3 (A B : Submodule S Ω) :
    IsLocalizedModule (nonZeroDivisors S) (spanQuotMap F A B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isLocalizedModule_spanQuotMap» := P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3
