-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_ringKrullDim_eq_two
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.ringKrullDim_eq_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:03.066089+00:00
-- url     : https://prove2.me/theorems/7554d569-1d44-4ffd-a850-3b80b00e2238
-- title:
--   Is Loc Data: ring Krull Dim eq two
-- statement:
--   The Is Loc Data construction uses the ring Krull Dim eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L364-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L364-L410

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.ringKrullDim_eq_two [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [V.IsPrime] (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f t : R} (hfV : f ∉ V) (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hft : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, W ≤ Z → t ∉ W) : ringKrullDim A = 2 := by sorry
