-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_map_maximalIdeal_le_maximal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:32.614821+00:00
-- url     : https://prove2.me/theorems/70ccc44e-648e-47bd-96d6-a9d4c8d252e5
-- title:
--   Finite Algebra Local Completion: map maximal Ideal le maximal
-- statement:
--   The Finite Algebra Local Completion construction uses the map maximal Ideal le maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L21-L26

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) (hn : n.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ n := by sorry
