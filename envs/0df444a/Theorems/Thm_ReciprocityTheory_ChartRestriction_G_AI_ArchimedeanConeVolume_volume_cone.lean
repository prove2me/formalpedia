-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_volume_cone
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:27.704613+00:00
-- url     : https://prove2.me/theorems/da7b068f-f6cd-59af-bfaf-de8173a828ec
-- title:
--   Archimedean Cone Volume: volume cone
-- statement:
--   The Archimedean Cone Volume construction uses the volume cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L190-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L190-L206

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone {u : E3} (hu : ‖u‖ = 1) {s : Set ℝ} (hs : MeasurableSet s) :
    volume {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by sorry
