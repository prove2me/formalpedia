-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ker_quot_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_ker_quot_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:01.957435+00:00
-- url     : https://prove2.me/theorems/d2e4e24c-6016-546c-86a8-637fc8d01235
-- title:
--   AI: length ker quot eq zero
-- statement:
--   The AI construction uses the length ker quot eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L312-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L312-L332

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_ker_quot_eq_zero {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) {x : A} (hx : x ∉ q.asIdeal) :
    length A (LinearMap.ker (LinearMap.lsmul A N x)) = 0 := by sorry
