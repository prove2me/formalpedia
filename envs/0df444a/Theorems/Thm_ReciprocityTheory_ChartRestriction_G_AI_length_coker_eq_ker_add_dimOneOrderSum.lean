-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_eq_ker_add_dimOneOrderSum
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_coker_eq_ker_add_dimOneOrderSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:56.249192+00:00
-- url     : https://prove2.me/theorems/4528945e-032e-4753-8dde-df41cbd0d66c
-- title:
--   AI: length coker eq ker add dim One Order Sum
-- statement:
--   The AI construction uses the length coker eq ker add dim One Order Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L372-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L372-L436

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_coker_eq_ker_add_dimOneOrderSum (hdim : ringKrullDim A = 1) (x : A) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    (∀ p ∈ support A M, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
      length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
        length A (LinearMap.ker (LinearMap.lsmul A M x)) + dimOneSum M x := by sorry
