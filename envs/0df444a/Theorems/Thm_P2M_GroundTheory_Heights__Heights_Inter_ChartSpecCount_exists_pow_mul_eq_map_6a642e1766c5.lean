-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_exists_pow_mul_eq_map_6a642e1766c5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_exists_pow_mul_eq_map_6a642e1766c5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:10.727635+00:00
-- url     : https://prove2.me/theorems/30410b7c-ab42-44d0-ae5a-a191f0a89df5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Spec Count exists pow mul eq map 6a642e1766c5: P2 M Ground Theory Heights  Heights Inter Chart Spec Count exists pow mul eq map 6a642e1766c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Spec Count exists pow mul eq map 6a642e1766c5 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Spec Count exists pow mul eq map 6a642e1766c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartSpecCount.lean#L15-L33

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_exists_pow_mul_eq_map_6a642e1766c5 {R : Type*} [CommRing R] (E : R) {Q : Type*}
    (F : MvPolynomial Q (Localization.Away E)) :
    ∃ (n : ℕ) (F' : MvPolynomial Q R),
      MvPolynomial.map (algebraMap R (Localization.Away E)) F' =
        MvPolynomial.C (algebraMap R (Localization.Away E) (E ^ n)) * F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartSpecCount».«exists_pow_mul_eq_map» := P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_exists_pow_mul_eq_map_6a642e1766c5
