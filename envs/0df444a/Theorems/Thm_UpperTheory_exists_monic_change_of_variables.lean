-- Prove2me | Theorems.Thm_UpperTheory_exists_monic_change_of_variables
-- name    : UpperTheory.exists_monic_change_of_variables
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:42.385798+00:00
-- url     : https://prove2.me/theorems/600d3997-4516-4192-afb2-216a5e6e2616
-- title:
--   Upper Theory: exists monic change of variables
-- statement:
--   The Upper Theory construction uses the exists monic change of variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NoetherNormalizationChart.lean#L81-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NoetherNormalizationChart.lean#L81-L118

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NoetherNormalizationChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open UpperTheory.NoetherNormalizationChart

theorem UpperTheory.exists_monic_change_of_variables :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) A), f ≠ 0 → ∃ (e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A)) (a : A), a ≠ 0 ∧ (e f).leadingCoeff = MvPolynomial.C a := by sorry
