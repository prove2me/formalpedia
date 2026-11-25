-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224
-- name    : P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:52.9108+00:00
-- url     : https://prove2.me/theorems/bab48b62-6f8d-4b28-b896-16b069088689
-- title:
--   P2 M Ground Theory Heights  Heights length localization maximal Ideal 74d266e6d224: P2 M Ground Theory Heights  Heights length localization maximal Ideal 74d266e6d224
-- statement:
--   The P2 M Ground Theory Heights  Heights length localization maximal Ideal 74d266e6d224 construction uses the P2 M Ground Theory Heights  Heights length localization maximal Ideal 74d266e6d224 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224 (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_localization_maximalIdeal» := P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224
