-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_mem_minimalPrimes_sup_of_le
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.mem_minimalPrimes_sup_of_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:59.934816+00:00
-- url     : https://prove2.me/theorems/c5d6e727-2de2-57e0-b28b-685fcd0dc09d
-- title:
--   Divisor Cycle Swap: mem minimal Primes sup of le
-- statement:
--   The Divisor Cycle Swap construction uses the mem minimal Primes sup of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L126-L131

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.mem_minimalPrimes_sup_of_le {V W Z : Ideal (MRingOver F ι)} {f t : MRingOver F ι}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes := by sorry
