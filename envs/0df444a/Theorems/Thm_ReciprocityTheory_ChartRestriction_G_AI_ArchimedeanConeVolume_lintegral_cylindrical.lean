-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_cylindrical
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_cylindrical
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:09.577795+00:00
-- url     : https://prove2.me/theorems/fbf32cbc-f0f4-4d04-9b4d-aa4b4d1c9bbc
-- title:
--   Archimedean Cone Volume: lintegral cylindrical
-- statement:
--   The Archimedean Cone Volume construction uses the lintegral cylindrical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L20-L33

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_cylindrical (H : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x : E3, H (x 0, (x 1, x 2)) = ∫⁻ z : ℝ, ∫⁻ p : ℝ × ℝ, H (z, p) := by sorry
