-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_equiv
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_coker_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:01.235903+00:00
-- url     : https://prove2.me/theorems/20d3e9c5-5144-4443-80fc-e6210de21f61
-- title:
--   AI: length coker equiv
-- statement:
--   The AI construction uses the length coker equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L281-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L281-L292

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_coker_equiv {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (e : N ≃ₗ[A] N') (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (N' ⧸ LinearMap.range (LinearMap.lsmul A N' x)) := by sorry
