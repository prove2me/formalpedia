-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_sum_ratDiv_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.sum_ratDiv_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:29.294061+00:00
-- url     : https://prove2.me/theorems/e629dbbe-f48f-41ec-8e2d-5c77c8d2854d
-- title:
--   Divisor Cycle Swap: sum rat Div eq
-- statement:
--   The Divisor Cycle Swap construction uses the sum rat Div eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L107-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L107-L119

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.sum_ratDiv_eq (V Z : Ideal (MRingOver F ι)) (f t : MRingOver F ι) :
    (ratDiv V f 1).sum (fun W m => m * ratDiv W t 1 Z) =
      ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℤ) := by sorry
