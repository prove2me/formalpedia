-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isProjVarF_of_mem_divSupp
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.isProjVarF_of_mem_divSupp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:45.624036+00:00
-- url     : https://prove2.me/theorems/7597a9d3-d83a-49d8-a79f-16e3cad740a9
-- title:
--   I1: is Proj Var F of mem div Supp
-- statement:
--   The I1 construction uses the is Proj Var F of mem div Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L294-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L294-L305

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.isProjVarF_of_mem_divSupp {V W : Ideal (MRingOver F ι)} {n : ℕ} {f : MRingOver F ι}
    {α : K → ℕ} (hV : IsProjVarF V (n + 1)) (hf : IsMultiHomog f α) (hfV : f ∉ V)
    (hW : W ∈ divSupp V f) : IsProjVarF W n := by sorry
