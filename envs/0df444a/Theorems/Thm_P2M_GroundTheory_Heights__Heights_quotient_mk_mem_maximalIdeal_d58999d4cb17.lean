-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17
-- name    : P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:55.904833+00:00
-- url     : https://prove2.me/theorems/f88182b8-2f6c-446d-876b-e7d2d345b12d
-- title:
--   P2 M Ground Theory Heights  Heights quotient mk mem maximal Ideal d58999d4cb17: P2 M Ground Theory Heights  Heights quotient mk mem maximal Ideal d58999d4cb17
-- statement:
--   The P2 M Ground Theory Heights  Heights quotient mk mem maximal Ideal d58999d4cb17 construction uses the P2 M Ground Theory Heights  Heights quotient mk mem maximal Ideal d58999d4cb17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L24-L36

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
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
open IsLocalRing CategoryTheory RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17 {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«quotient_mk_mem_maximalIdeal» := P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17
