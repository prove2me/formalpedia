-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_integral_sphere_isometry
-- name    : ReciprocityTheory.ChartRestriction.G.AI.integral_sphere_isometry
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:10.881359+00:00
-- url     : https://prove2.me/theorems/e572a0d5-0df0-49c0-a7cd-fac75cfd8af3
-- title:
--   AI: integral sphere isometry
-- statement:
--   The AI construction uses the integral sphere isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L7-L16

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

theorem ReciprocityTheory.ChartRestriction.G.AI.integral_sphere_isometry (L : E3 ≃ₗᵢ[ℝ] E3) (F : E3 → ℝ)
    (hF : Integrable (fun n : S2 => F n) sphereMeasure) :
    ∫ n : S2, F (L n) ∂sphereMeasure = ∫ n : S2, F n ∂sphereMeasure := by sorry
