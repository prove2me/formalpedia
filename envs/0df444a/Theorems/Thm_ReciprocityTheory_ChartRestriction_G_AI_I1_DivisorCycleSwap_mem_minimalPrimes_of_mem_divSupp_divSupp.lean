-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_mem_minimalPrimes_of_mem_divSupp_divSupp
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.mem_minimalPrimes_of_mem_divSupp_divSupp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:34.567268+00:00
-- url     : https://prove2.me/theorems/42f25e83-5429-4300-8cdc-916e541e70fa
-- title:
--   Divisor Cycle Swap: mem minimal Primes of mem div Supp div Supp
-- statement:
--   The Divisor Cycle Swap construction uses the mem minimal Primes of mem div Supp div Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L133-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L133-L156

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
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.mem_minimalPrimes_of_mem_divSupp_divSupp {V W Z : Ideal (MRingOver F ι)} {n : ℕ}
    {f t : MRingOver F ι} {α β : K → ℕ} (hV : IsProjVarF V (n + 2)) (hf : IsMultiHomog f α)
    (ht : IsMultiHomog t β) (hfV : f ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W)
    (hW : W ∈ divSupp V f) (hZ : Z ∈ divSupp W t) :
    Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes := by sorry
