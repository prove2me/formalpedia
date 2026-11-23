-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_idempotent_henselian
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_idempotent_henselian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:24.006323+00:00
-- url     : https://prove2.me/theorems/6f844aef-4f6b-4b0f-a4e3-2daaae87e28e
-- title:
--   Finite Algebra Local Completion: exists idempotent henselian
-- statement:
--   The Finite Algebra Local Completion construction uses the exists idempotent henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L65-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L65-L122

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_idempotent_henselian {S : Type*} [CommRing S] (J : Ideal S) [HenselianRing S J] (x : S) (N : ℕ)
    (hN : (x * x - x) ^ (N + 1) ∈ J) : ∃ e s : S, e * e = e ∧ e - x = s * (x * x - x) := by sorry
