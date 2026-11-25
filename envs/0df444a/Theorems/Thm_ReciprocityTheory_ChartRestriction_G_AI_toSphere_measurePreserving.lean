-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_toSphere_measurePreserving
-- name    : ReciprocityTheory.ChartRestriction.G.AI.toSphere_measurePreserving
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:53.486019+00:00
-- url     : https://prove2.me/theorems/02cc5e9f-5fde-4429-ac83-5e20d51956e3
-- title:
--   AI: to Sphere measure Preserving
-- statement:
--   The AI construction uses the to Sphere measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L28-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI

theorem ReciprocityTheory.ChartRestriction.G.AI.toSphere_measurePreserving (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by sorry
