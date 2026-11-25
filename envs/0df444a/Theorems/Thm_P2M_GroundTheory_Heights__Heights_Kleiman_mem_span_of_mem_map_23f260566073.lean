-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_span_of_mem_map_23f260566073
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_span_of_mem_map_23f260566073
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:08.767854+00:00
-- url     : https://prove2.me/theorems/dd502ed9-5d32-5e64-a0a4-9787fe4d5f35
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem span of mem map 23f260566073: P2 M Ground Theory Heights  Heights Kleiman mem span of mem map 23f260566073
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem span of mem map 23f260566073 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem span of mem map 23f260566073 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L91-L108

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
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_span_of_mem_map_23f260566073 (qq : Ideal (Poly S N)) {f : Poly F N}
    (hf : f ∈ qq.map (MvPolynomial.map (algebraMap S F))) :
    f ∈ Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_span_of_mem_map» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_span_of_mem_map_23f260566073
