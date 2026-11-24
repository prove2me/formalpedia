-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_measurableSet_cone0
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.measurableSet_cone0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:19.75861+00:00
-- url     : https://prove2.me/theorems/1021a68f-a669-4ff8-9ff5-c329a0794682
-- title:
--   Archimedean Cone Volume: measurable Set cone0
-- statement:
--   The Archimedean Cone Volume construction uses the measurable Set cone0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L153-L157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.measurableSet_cone0 {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} := by sorry
