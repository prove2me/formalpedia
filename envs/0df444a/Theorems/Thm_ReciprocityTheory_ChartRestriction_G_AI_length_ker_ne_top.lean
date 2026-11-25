-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ker_ne_top
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_ker_ne_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:23.919493+00:00
-- url     : https://prove2.me/theorems/0984e50a-2824-5334-8bfb-e577c7891da8
-- title:
--   AI: length ker ne top
-- statement:
--   The AI construction uses the length ker ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L95-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
universe u

theorem ReciprocityTheory.ChartRestriction.G.AI.length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by sorry
