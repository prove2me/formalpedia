-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_dvd_map_of_dvd_map_7571100aeae2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_dvd_map_of_dvd_map_7571100aeae2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:05.444818+00:00
-- url     : https://prove2.me/theorems/56faedb5-f3e4-4993-ba19-2137a4523e40
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Spec Count dvd map of dvd map 7571100aeae2: P2 M Ground Theory Heights  Heights Inter Chart Spec Count dvd map of dvd map 7571100aeae2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Spec Count dvd map of dvd map 7571100aeae2 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Spec Count dvd map of dvd map 7571100aeae2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L50-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocAwaySpec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartSpecCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Polynomial
open GroundTheory.Heights₂.Heights.Inter.ChartSpecCount

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_dvd_map_of_dvd_map_7571100aeae2 {A Φ K : Type*} [CommRing A] [Field Φ] [CommRing K] (fA : A →+* Φ) (σ : A →+* K)
    (hker : RingHom.ker fA ≤ RingHom.ker σ) {mA : A[X]} (hm : mA.Monic) {p : A[X]}
    (hp : mA.map fA ∣ p.map fA) : mA.map σ ∣ p.map σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartSpecCount».«dvd_map_of_dvd_map» := P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_dvd_map_of_dvd_map_7571100aeae2
