-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_quot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.quot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:20.921664+00:00
-- url     : https://prove2.me/theorems/61504324-5fbc-4917-9171-6fd6c004c09b
-- title:
--   Is Loc Data: quot
-- statement:
--   The Is Loc Data construction uses the quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L174-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L174-L185

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.quot (h : IsLocData R T S V) (P : Ideal T) :
    IsLocData R (T ⧸ P) S (P.comap (algebraMap R T)) := by sorry
