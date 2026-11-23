-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_finite_of_fibre
-- name    : ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:09.33294+00:00
-- url     : https://prove2.me/theorems/5192bb30-5fc4-47e9-8f5f-82ffe646488a
-- title:
--   Prime Avoidance Fibre: finite of fibre
-- statement:
--   The Prime Avoidance Fibre construction uses the finite of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PrimeAvoidanceFibre.lean#L47-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PrimeAvoidanceFibre.lean#L47-L118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpanTopOfComplete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by sorry
