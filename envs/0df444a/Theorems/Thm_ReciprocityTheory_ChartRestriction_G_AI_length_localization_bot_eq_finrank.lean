-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_localization_bot_eq_finrank
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_localization_bot_eq_finrank
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:03.173136+00:00
-- url     : https://prove2.me/theorems/f53a7ff1-e16a-48f0-8622-e1922953ebd3
-- title:
--   AI: length localization bot eq finrank
-- statement:
--   The AI construction uses the length localization bot eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L78-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L78-L93

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_localization_bot_eq_finrank (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    length (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) =
      (finrank A M : ℕ∞) := by sorry
