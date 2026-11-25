-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_not_lt_lt_of_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.not_lt_lt_of_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:51.235213+00:00
-- url     : https://prove2.me/theorems/8b8ed495-09a7-45b2-9038-9258cd325100
-- title:
--   I1: not lt lt of mem minimal Primes
-- statement:
--   The I1 construction uses the not lt lt of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L13-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L13-L45

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.not_lt_lt_of_mem_minimalPrimes {V W W' : Ideal (MRingOver F ι)} [V.IsPrime] [W'.IsPrime]
    {x : MRingOver F ι} (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W')
    (hW'W : W' < W) : False := by sorry
