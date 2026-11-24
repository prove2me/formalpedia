-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_integrable_mul_inner
-- name    : ReciprocityTheory.ChartRestriction.G.AI.integrable_mul_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:01.082797+00:00
-- url     : https://prove2.me/theorems/48bb90b4-bb46-4228-be66-22fcb0040f4a
-- title:
--   AI: integrable mul inner
-- statement:
--   The AI construction uses the integrable mul inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L18-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.AI.integrable_mul_inner {F : S2 → ℝ} (hF : Integrable F sphereMeasure) (v : E3) :
    Integrable (fun n : S2 => F n * inner ℝ (n : E3) v) sphereMeasure := by sorry
