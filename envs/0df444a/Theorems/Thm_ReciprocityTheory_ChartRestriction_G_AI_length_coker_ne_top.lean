-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_ne_top
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:36.71588+00:00
-- url     : https://prove2.me/theorems/c10ce60d-8e86-4108-b822-2526c8a4cd17
-- title:
--   AI: length coker ne top
-- statement:
--   The AI construction uses the length coker ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L27-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L27-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Ring.KrullDimLE 1 A] {x : A} (hx : x ≠ 0) :
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ := by sorry
