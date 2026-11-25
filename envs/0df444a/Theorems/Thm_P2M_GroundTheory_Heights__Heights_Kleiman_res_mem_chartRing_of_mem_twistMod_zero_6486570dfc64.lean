-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:23.784382+00:00
-- url     : https://prove2.me/theorems/bf79231e-a583-4e19-840b-450407d47d84
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res mem chart Ring of mem twist Mod zero 6486570dfc64: P2 M Ground Theory Heights  Heights Kleiman res mem chart Ring of mem twist Mod zero 6486570dfc64
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res mem chart Ring of mem twist Mod zero 6486570dfc64 construction uses the P2 M Ground Theory Heights  Heights Kleiman res mem chart Ring of mem twist Mod zero 6486570dfc64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L16-L21

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64 {I : Chart x} {a : Ω} (ha : a ∈ twistMod S x 0 I) :
    a ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_mem_chartRing_of_mem_twistMod_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64
