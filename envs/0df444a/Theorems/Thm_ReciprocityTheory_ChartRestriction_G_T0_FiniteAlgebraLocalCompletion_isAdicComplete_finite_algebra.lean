-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isAdicComplete_finite_algebra
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:43.939568+00:00
-- url     : https://prove2.me/theorems/b3b46b5d-082b-43b9-a21c-dc9993b1f4ee
-- title:
--   Finite Algebra Local Completion: is Adic Complete finite algebra
-- statement:
--   The Finite Algebra Local Completion construction uses the is Adic Complete finite algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L14-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by sorry
