-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ordQuotient_bot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.ordQuotient_bot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:01.529625+00:00
-- url     : https://prove2.me/theorems/a7a7d8bb-b857-500e-b709-0ae8b0f50373
-- title:
--   AI: ord Quotient bot
-- statement:
--   The AI construction uses the ord Quotient bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L95-L107

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

theorem ReciprocityTheory.ChartRestriction.G.AI.ordQuotient_bot (x : A) :
    ordMod ⟨⊥, Ideal.isPrime_bot⟩ x = Ring.ord A x := by sorry
