-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_maximalIdeal_of_quotient_mk_4d5502ea0542
-- name    : P2M_GroundTheory_Heights__Heights_mem_maximalIdeal_of_quotient_mk_4d5502ea0542
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:25.630852+00:00
-- url     : https://prove2.me/theorems/aba04211-9f96-4af4-970b-cf31c7d899ce
-- title:
--   P2 M Ground Theory Heights  Heights mem maximal Ideal of quotient mk 4d5502ea0542: P2 M Ground Theory Heights  Heights mem maximal Ideal of quotient mk 4d5502ea0542
-- statement:
--   The P2 M Ground Theory Heights  Heights mem maximal Ideal of quotient mk 4d5502ea0542 construction uses the P2 M Ground Theory Heights  Heights mem maximal Ideal of quotient mk 4d5502ea0542 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L38-L41

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

theorem P2M_GroundTheory_Heights__Heights_mem_maximalIdeal_of_quotient_mk_4d5502ea0542 {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_maximalIdeal_of_quotient_mk» := P2M_GroundTheory_Heights__Heights_mem_maximalIdeal_of_quotient_mk_4d5502ea0542
