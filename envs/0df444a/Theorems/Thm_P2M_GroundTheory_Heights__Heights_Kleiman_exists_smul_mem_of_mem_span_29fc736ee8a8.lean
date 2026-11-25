-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:03:22.687851+00:00
-- url     : https://prove2.me/theorems/c970d2d1-c8ee-5d02-8b3a-ef42aac3c056
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists smul mem of mem span 29fc736ee8a8: P2 M Ground Theory Heights  Heights Kleiman exists smul mem of mem span 29fc736ee8a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists smul mem of mem span 29fc736ee8a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists smul mem of mem span 29fc736ee8a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L21-L40

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8 (P : Submodule S Ω) {z : Ω}
    (hz : z ∈ Submodule.span F (P : Set Ω)) : ∃ t ∈ nonZeroDivisors S, t • z ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_smul_mem_of_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8
