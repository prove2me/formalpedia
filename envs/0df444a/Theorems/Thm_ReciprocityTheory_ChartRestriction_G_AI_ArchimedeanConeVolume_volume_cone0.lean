-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_volume_cone0
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:41.927418+00:00
-- url     : https://prove2.me/theorems/9ce8310b-0bf9-4681-b11e-bfbae0708235
-- title:
--   Archimedean Cone Volume: volume cone0
-- statement:
--   The Archimedean Cone Volume construction uses the volume cone0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L159-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L159-L188

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone0 {s : Set ℝ} (hs : MeasurableSet s) :
    volume {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by sorry
