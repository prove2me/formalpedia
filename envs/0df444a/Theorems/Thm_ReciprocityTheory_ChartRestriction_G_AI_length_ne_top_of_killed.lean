-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ne_top_of_killed
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_of_killed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:07.572521+00:00
-- url     : https://prove2.me/theorems/27c51c53-ed98-4a63-9a8d-3be009d23a44
-- title:
--   AI: length ne top of killed
-- statement:
--   The AI construction uses the length ne top of killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L69-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L69-L93

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by sorry
