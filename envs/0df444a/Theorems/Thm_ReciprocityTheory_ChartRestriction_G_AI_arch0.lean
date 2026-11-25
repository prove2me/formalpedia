-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_arch0
-- name    : ReciprocityTheory.ChartRestriction.G.AI.arch0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:15.427629+00:00
-- url     : https://prove2.me/theorems/551babc7-ed4e-4870-aac7-fa17ef28cb25
-- title:
--   AI: arch0
-- statement:
--   The AI construction uses the arch0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L267-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L267-L280

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

theorem ReciprocityTheory.ChartRestriction.G.AI.arch0 (u : E3) (f : ℝ → ℝ) (hu : ‖u‖ = 1) (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) :
    MeasureTheory.Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    ∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t := by sorry
