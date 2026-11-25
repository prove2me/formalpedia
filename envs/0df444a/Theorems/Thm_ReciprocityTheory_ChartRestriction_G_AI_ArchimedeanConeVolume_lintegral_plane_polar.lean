-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_plane_polar
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_plane_polar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:33.59664+00:00
-- url     : https://prove2.me/theorems/5d91a0bb-4c6e-438c-9407-7fbe3b0799de
-- title:
--   Archimedean Cone Volume: lintegral plane polar
-- statement:
--   The Archimedean Cone Volume construction uses the lintegral plane polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean#L35-L39

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_plane_polar (K : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, K p =
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal q.1 * K (q.1 * cos q.2, q.1 * sin q.2) := by sorry
