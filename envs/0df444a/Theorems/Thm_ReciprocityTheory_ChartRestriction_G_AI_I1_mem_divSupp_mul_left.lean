-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_divSupp_mul_left
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.mem_divSupp_mul_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:37.59575+00:00
-- url     : https://prove2.me/theorems/f5910461-da9a-57a3-8f31-34922f030502
-- title:
--   I1: mem div Supp mul left
-- statement:
--   The I1 construction uses the mem div Supp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L171-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L171-L178

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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.mem_divSupp_mul_left {V W : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g : MRingOver F ι}
    (hgV : g ∉ V) (hW : W ∈ divSupp V f) : W ∈ divSupp V (f * g) := by sorry
