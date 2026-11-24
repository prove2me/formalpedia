-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_atPrime
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.atPrime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:23.226368+00:00
-- url     : https://prove2.me/theorems/7098b136-9fa9-4577-a737-700ad3b91e49
-- title:
--   Is Loc Data: at Prime
-- statement:
--   The Is Loc Data construction uses the at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L134-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L134-L172

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
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {S : Submonoid R} {V : Ideal R}

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.atPrime (h : IsLocData R T S V) (P : Ideal T) [hP : P.IsPrime] :
    IsLocData R (Localization.AtPrime P) (P.comap (algebraMap R T)).primeCompl V := by sorry
