-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_isLocData_atPrime_quot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:19.443105+00:00
-- url     : https://prove2.me/theorems/c96890ef-3025-4f06-9a7e-dfb0a134767c
-- title:
--   Swap Loc: is Loc Data at Prime quot
-- statement:
--   The Swap Loc construction uses the is Loc Data at Prime quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L88-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L88-L123

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot {R : Type*} [CommRing R] (V Z : Ideal R) [Z.IsPrime]
    (hVZ : V ≤ Z) [(Z.map (Ideal.Quotient.mk V)).IsPrime] :
    IsLocData R (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) Z.primeCompl V := by sorry
