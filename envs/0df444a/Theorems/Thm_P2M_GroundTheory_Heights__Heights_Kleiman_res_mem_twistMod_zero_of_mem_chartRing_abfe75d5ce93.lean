-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:24:49.672069+00:00
-- url     : https://prove2.me/theorems/d515e386-2f83-49fe-b86c-8e78487c6c48
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res mem twist Mod zero of mem chart Ring abfe75d5ce93: P2 M Ground Theory Heights  Heights Kleiman res mem twist Mod zero of mem chart Ring abfe75d5ce93
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res mem twist Mod zero of mem chart Ring abfe75d5ce93 construction uses the P2 M Ground Theory Heights  Heights Kleiman res mem twist Mod zero of mem chart Ring abfe75d5ce93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93 {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ twistMod S x 0 I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_mem_twistMod_zero_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93
