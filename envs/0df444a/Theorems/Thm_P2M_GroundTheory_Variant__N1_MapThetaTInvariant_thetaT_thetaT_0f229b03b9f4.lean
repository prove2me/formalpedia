-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4
-- name    : P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:26.303269+00:00
-- url     : https://prove2.me/theorems/6ebcf313-67a6-4b34-9442-b65574ed2f24
-- title:
--   P2 M Ground Theory Variant  N1 Map Theta TInvariant theta T theta T 0f229b03b9f4: P2 M Ground Theory Variant  N1 Map Theta TInvariant theta T theta T 0f229b03b9f4
-- statement:
--   The P2 M Ground Theory Variant  N1 Map Theta TInvariant theta T theta T 0f229b03b9f4 construction uses the P2 M Ground Theory Variant  N1 Map Theta TInvariant theta T theta T 0f229b03b9f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
open GroundTheory.Variant₂.N1.MapThetaTInvariant
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
open GroundTheory.Automorphic.ContragredientTranspose

theorem P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4 {F : Type*} [Field F] {n : ℕ} (g : GL (Fin n) F) :
    (thetaT : GL (Fin n) F ≃* GL (Fin n) F) (thetaT g) = g := by sorry

alias «GroundTheory».«Variant₂».«N1».«MapThetaTInvariant».«thetaT_thetaT» := P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4
