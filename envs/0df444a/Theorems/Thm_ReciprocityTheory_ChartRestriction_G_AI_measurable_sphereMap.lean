-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_measurable_sphereMap
-- name    : ReciprocityTheory.ChartRestriction.G.AI.measurable_sphereMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:25.612737+00:00
-- url     : https://prove2.me/theorems/3b4079ea-4015-4559-8abc-5371b3323447
-- title:
--   AI: measurable sphere Map
-- statement:
--   The AI construction uses the measurable sphere Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KappaA.lean#L25-L26

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

theorem ReciprocityTheory.ChartRestriction.G.AI.measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := by sorry
