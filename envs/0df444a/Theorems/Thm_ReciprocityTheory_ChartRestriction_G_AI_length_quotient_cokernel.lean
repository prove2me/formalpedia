-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quotient_cokernel
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_quotient_cokernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:39.255546+00:00
-- url     : https://prove2.me/theorems/3b30db43-7d98-5a56-a346-26646ebe1627
-- title:
--   AI: length quotient cokernel
-- statement:
--   The AI construction uses the length quotient cokernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthTwoGeneratorQuotient.lean#L28-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthTwoGeneratorQuotient.lean#L28-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthTwoGeneratorQuotient
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
universe u
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_quotient_cokernel (a b : A) :
    length (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (A ⧸ Ideal.span {a, b}) := by sorry
