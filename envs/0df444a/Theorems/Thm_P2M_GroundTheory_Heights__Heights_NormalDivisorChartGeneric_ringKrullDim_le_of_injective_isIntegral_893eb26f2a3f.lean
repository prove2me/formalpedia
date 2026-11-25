-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_ringKrullDim_le_of_injective_isIntegral_893eb26f2a3f
-- name    : P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_ringKrullDim_le_of_injective_isIntegral_893eb26f2a3f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:07.158708+00:00
-- url     : https://prove2.me/theorems/38c297bd-ce3b-4091-9928-8c0a4bdd227f
-- title:
--   P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic ring Krull Dim le of injective is Integral 893eb26f2a3f: P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic ring Krull Di
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic ring Krull Dim le of injective is Integral 893eb26f2a3f construction uses the P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic ring Krull Dim le of injective is Integral 893eb26f2a3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDivisorChartGeneric.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDivisorChartGeneric.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDivisorChartGeneric
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDivisorChartGeneric

theorem P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_ringKrullDim_le_of_injective_isIntegral_893eb26f2a3f {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDivisorChartGeneric».«ringKrullDim_le_of_injective_isIntegral» := P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_ringKrullDim_le_of_injective_isIntegral_893eb26f2a3f
