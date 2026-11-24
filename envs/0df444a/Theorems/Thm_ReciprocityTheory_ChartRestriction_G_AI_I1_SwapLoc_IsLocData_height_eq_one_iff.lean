-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_height_eq_one_iff
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.height_eq_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:19.825905+00:00
-- url     : https://prove2.me/theorems/a750e101-a1e6-4993-b79e-1cc5c25cc250
-- title:
--   Is Loc Data: height eq one iff
-- statement:
--   The Is Loc Data construction uses the height eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L290-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L290-L335

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.height_eq_one_iff [IsDomain A] [IsNoetherianRing A] [V.IsPrime]
    (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f : R} (hfV : f ∉ V) (p : Ideal A) [hp : p.IsPrime] :
    (p.height = 1 ∧ algebraMap R A f ∈ p) ↔
      p.comap (algebraMap R A) ∈ (V ⊔ Ideal.span {f}).minimalPrimes := by sorry
