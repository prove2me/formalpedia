-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_exists_prime_comap_atPrime_quot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.exists_prime_comap_atPrime_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:14.119498+00:00
-- url     : https://prove2.me/theorems/f4041fca-c6ef-4208-80a1-1f890f5e4ff5
-- title:
--   Swap Loc: exists prime comap at Prime quot
-- statement:
--   The Swap Loc construction uses the exists prime comap at Prime quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L228-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean#L228-L250

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.exists_prime_comap_atPrime_quot {R : Type*} [CommRing R] (V Z : Ideal R)
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] (Q : Ideal R) (hQ : Q.IsPrime) (hVQ : V ≤ Q)
    (hQZ : Q ≤ Z) :
    ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
      p.comap (algebraMap R _) = Q := by sorry
