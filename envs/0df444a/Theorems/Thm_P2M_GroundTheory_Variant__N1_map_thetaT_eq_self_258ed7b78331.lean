-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331
-- name    : P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:42.068459+00:00
-- url     : https://prove2.me/theorems/38790fb0-1058-45ac-ae5a-c3df2402ee63
-- title:
--   P2 M Ground Theory Variant  N1 map theta T eq self 258ed7b78331: P2 M Ground Theory Variant  N1 map theta T eq self 258ed7b78331
-- statement:
--   The P2 M Ground Theory Variant  N1 map theta T eq self 258ed7b78331 construction uses the P2 M Ground Theory Variant  N1 map theta T eq self 258ed7b78331 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L89-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L89-L121

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
open MapThetaTInvariant
open GroundTheory.Automorphic.ContragredientTranspose

theorem P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331 {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
    [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    Measure.map (⇑thetaT) μ = μ := by sorry

alias «GroundTheory».«Variant₂».«N1».«map_thetaT_eq_self» := P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331
