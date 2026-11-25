-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_Ioi_ofReal_mul
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_Ioi_ofReal_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:47.204826+00:00
-- url     : https://prove2.me/theorems/0243ef6e-d4f1-491f-b9ab-c0ba6e3f0cbd
-- title:
--   Archimedean Cone Volume: lintegral Ioi of Real mul
-- statement:
--   The Archimedean Cone Volume construction uses the lintegral Ioi of Real mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L67-L74

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_Ioi_ofReal_mul (F : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r = ∫⁻ r, ENNReal.ofReal r * F r := by sorry
