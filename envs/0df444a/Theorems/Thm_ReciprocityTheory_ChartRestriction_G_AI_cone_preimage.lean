-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_cone_preimage
-- name    : ReciprocityTheory.ChartRestriction.G.AI.cone_preimage
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:50.032944+00:00
-- url     : https://prove2.me/theorems/4038930e-12c5-5f7f-a462-ae58c750ad46
-- title:
--   AI: cone preimage
-- statement:
--   The AI construction uses the cone preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L8-L23

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

theorem ReciprocityTheory.ChartRestriction.G.AI.cone_preimage (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by sorry
