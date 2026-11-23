-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isPrecomplete_finite_module
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:36.815773+00:00
-- url     : https://prove2.me/theorems/5a51a10d-e56d-4fbf-8187-d044125899c4
-- title:
--   Finite Algebra Local Completion: is Precomplete finite module
-- statement:
--   The Finite Algebra Local Completion construction uses the is Precomplete finite module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L10-L12

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by sorry
