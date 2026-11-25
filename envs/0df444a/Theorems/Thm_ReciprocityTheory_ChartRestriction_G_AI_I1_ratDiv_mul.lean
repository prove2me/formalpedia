-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_ratDiv_mul
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:42.341925+00:00
-- url     : https://prove2.me/theorems/cf00e7ae-88d2-5a08-bbe2-d7ebc13ac351
-- title:
--   I1: rat Div mul
-- statement:
--   The I1 construction uses the rat Div mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L221-L226

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv_mul {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g f' g' : MRingOver F ι}
    (hf : f ∉ V) (hg : g ∉ V) (hf' : f' ∉ V) (hg' : g' ∉ V) :
    ratDiv V (f * f') (g * g') = ratDiv V f g + ratDiv V f' g' := by sorry
