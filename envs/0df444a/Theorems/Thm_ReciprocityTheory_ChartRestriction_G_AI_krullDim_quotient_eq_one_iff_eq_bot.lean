-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDim_quotient_eq_one_iff_eq_bot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.krullDim_quotient_eq_one_iff_eq_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:15.879016+00:00
-- url     : https://prove2.me/theorems/9545abc0-cdbc-5bac-b4a2-72608ad5ebb4
-- title:
--   AI: krull Dim quotient eq one iff eq bot
-- statement:
--   The AI construction uses the krull Dim quotient eq one iff eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L14-L25

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

theorem ReciprocityTheory.ChartRestriction.G.AI.krullDim_quotient_eq_one_iff_eq_bot [Ring.KrullDimLE 1 A] (h : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 ↔ p.asIdeal = ⊥ := by sorry
