-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment2_inv
-- name    : ReciprocityTheory.ChartRestriction.G.AI.moment2_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:53.586503+00:00
-- url     : https://prove2.me/theorems/494947c6-db3e-47a1-873f-1f4b74edde69
-- title:
--   AI: moment2 inv
-- statement:
--   The AI construction uses the moment2 inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L47-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L47-L59

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
variable {u : E3} {f : ℝ → ℝ}

theorem ReciprocityTheory.ChartRestriction.G.AI.moment2_inv (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    (L : E3 ≃ₗᵢ[ℝ] E3) (hL : L u = u) (v w : E3) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (L v) * inner ℝ (n : E3) (L w)
        ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w
        ∂sphereMeasure := by sorry
