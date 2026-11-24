-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_maximalIdeal_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.maximalIdeal_mem_minimalPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:04.747434+00:00
-- url     : https://prove2.me/theorems/095e685a-068b-4779-b117-f733c2cc4146
-- title:
--   Is Loc Data: maximal Ideal mem minimal Primes
-- statement:
--   The Is Loc Data construction uses the maximal Ideal mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L337-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L337-L362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R}
  {V Z : Ideal R} [Z.IsPrime]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.maximalIdeal_mem_minimalPrimes [IsLocalRing A]
    (h : IsLocData R A Z.primeCompl V) (hZex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z)
    {f t : R} (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) :
    IsLocalRing.maximalIdeal A ∈
      (Ideal.span {algebraMap R A f, algebraMap R A t}).minimalPrimes := by sorry
