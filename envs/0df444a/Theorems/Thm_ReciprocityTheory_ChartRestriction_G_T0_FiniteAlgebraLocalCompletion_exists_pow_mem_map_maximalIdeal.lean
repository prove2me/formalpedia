-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_pow_mem_map_maximalIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:51.127571+00:00
-- url     : https://prove2.me/theorems/c1c2a523-b39c-4227-b635-6867d9b73cc0
-- title:
--   Finite Algebra Local Completion: exists pow mem map maximal Ideal
-- statement:
--   The Finite Algebra Local Completion construction uses the exists pow mem map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L46-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L46-L63

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (b : S) (hb : ∀ n : Ideal S, n.IsMaximal → b ∈ n) :
    ∃ N : ℕ, 0 < N ∧ b ^ N ∈ (maximalIdeal R).map (algebraMap R S) := by sorry
