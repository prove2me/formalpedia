-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_sum_eq_finsum
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.sum_eq_finsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:59.144378+00:00
-- url     : https://prove2.me/theorems/70555677-d192-47e8-a5e7-6990f59a5ea1
-- title:
--   Divisor Cycle Swap: sum eq finsum
-- statement:
--   The Divisor Cycle Swap construction uses the sum eq finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L169-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L169-L219

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.sum_eq_finsum {V Z : Ideal (MRingOver F ι)} [V.IsPrime] [hZp : Z.IsPrime]
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] {f t : MRingOver F ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
        (_ : p.asIdeal.height = 1 ∧
          algebraMap (MRingOver F ι) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) f ∈
            p.asIdeal),
        ordLoc p (algebraMap (MRingOver F ι) _ f) * ordMod p (algebraMap (MRingOver F ι) _ t) := by sorry
