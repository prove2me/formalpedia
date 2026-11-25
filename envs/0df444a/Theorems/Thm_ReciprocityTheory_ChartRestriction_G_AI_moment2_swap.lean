-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment2_swap
-- name    : ReciprocityTheory.ChartRestriction.G.AI.moment2_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:38.995356+00:00
-- url     : https://prove2.me/theorems/31ab7f4c-46bd-41c0-b11d-3dfc5751fc00
-- title:
--   AI: moment2 swap
-- statement:
--   The AI construction uses the moment2 swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L89-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaB.lean#L89-L99

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

theorem ReciprocityTheory.ChartRestriction.G.AI.moment2_swap (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    {a c : E3} (ha : inner ℝ a u = 0) (hc : inner ℝ c u = 0) (hac : ‖a‖ = ‖c‖) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) c * inner ℝ (n : E3) c ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a * inner ℝ (n : E3) a
        ∂sphereMeasure := by sorry
