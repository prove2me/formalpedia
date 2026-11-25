-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_not_mem_of_mem_divSupp_swap
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.not_mem_of_mem_divSupp_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:21.711012+00:00
-- url     : https://prove2.me/theorems/de9730dc-af5f-4c23-9ec5-5ace0ffe543d
-- title:
--   I1: not mem of mem div Supp swap
-- statement:
--   The I1 construction uses the not mem of mem div Supp swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L47-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.not_mem_of_mem_divSupp_swap {V W : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι}
    {α β : K → ℕ} (hV : IsProjVarF V (n + 1)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β)
    (hfV : f ∉ V) (htV : t ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W) (hW : W ∈ divSupp V t) :
    f ∉ W := by sorry
