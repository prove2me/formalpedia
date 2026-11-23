-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_FinitelyGeneratedModPow_fg_mod_pow
-- name    : UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:46.994171+00:00
-- url     : https://prove2.me/theorems/97b7d61d-84d7-4e66-bfa2-c1e845b3df50
-- title:
--   Finitely Generated Mod Pow: fg mod pow
-- statement:
--   The Finitely Generated Mod Pow construction uses the fg mod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FinitelyGeneratedModPow.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FinitelyGeneratedModPow.lean#L5-L42

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitelyGeneratedModPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.FinitelyGeneratedModPow

theorem UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by sorry
