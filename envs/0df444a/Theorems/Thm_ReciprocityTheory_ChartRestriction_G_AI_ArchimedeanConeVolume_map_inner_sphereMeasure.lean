-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_map_inner_sphereMeasure
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.map_inner_sphereMeasure
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:35.952365+00:00
-- url     : https://prove2.me/theorems/09c5e093-7fa5-4dd8-89e7-7a2d15b043b6
-- title:
--   Archimedean Cone Volume: map inner sphere Measure
-- statement:
--   The Archimedean Cone Volume construction uses the map inner sphere Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L234-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L234-L259

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.map_inner_sphereMeasure {u : E3} (hu : ‖u‖ = 1) :
    sphereMeasure.map (fun n : S2 => inner ℝ (n : E3) u) =
      (2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1) := by sorry
