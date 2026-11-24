-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_maximalIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.comap_maximalIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:08.060805+00:00
-- url     : https://prove2.me/theorems/f0511ae5-0431-4f62-86df-6c035911a8bd
-- title:
--   Is Loc Data: comap maximal Ideal
-- statement:
--   The Is Loc Data construction uses the comap maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L282-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L282-L288

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.comap_maximalIdeal [IsLocalRing A] (h : IsLocData R A Z.primeCompl V)
    (hex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z) :
    (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = Z := by sorry
