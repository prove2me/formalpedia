-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_coneFun
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_coneFun
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:58.413388+00:00
-- url     : https://prove2.me/theorems/78a1adc9-ca06-4551-bbdd-331caa23c5fe
-- title:
--   Archimedean Cone Volume: lintegral cone Fun
-- statement:
--   The Archimedean Cone Volume construction uses the lintegral cone Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L76-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L76-L143

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_coneFun (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x : E3, coneFun G (x 0) ((x 1) ^ 2 + (x 2) ^ 2) =
      volume (Ioo (-π) π) * (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r) *
        ∫⁻ t in Ioo (-1 : ℝ) 1, G t := by sorry
