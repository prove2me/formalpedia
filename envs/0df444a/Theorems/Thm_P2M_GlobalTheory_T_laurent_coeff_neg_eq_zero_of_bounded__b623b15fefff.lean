-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_laurent_coeff_neg_eq_zero_of_bounded__b623b15fefff
-- name    : P2M_GlobalTheory_T_laurent_coeff_neg_eq_zero_of_bounded__b623b15fefff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:00.177935+00:00
-- url     : https://prove2.me/theorems/0398587a-d9cd-5d07-84c6-c6b39d97f291
-- title:
--   P2 M Global Theory T laurent coeff neg eq zero of bounded  b623b15fefff: P2 M Global Theory T laurent coeff neg eq zero of bounded  b623b15fefff
-- statement:
--   The P2 M Global Theory T laurent coeff neg eq zero of bounded  b623b15fefff construction uses the P2 M Global Theory T laurent coeff neg eq zero of bounded  b623b15fefff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBoundedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBoundedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_laurent_coeff_neg_eq_zero_of_bounded__b623b15fefff : ∀ (F : ℂ⸨X⸩) (T C : ℝ), (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) → ∀ m : ℤ, m < 0 → F.coeff m = 0 := by sorry

alias «GlobalTheory».«T».«laurent_coeff_neg_eq_zero_of_bounded'» := P2M_GlobalTheory_T_laurent_coeff_neg_eq_zero_of_bounded__b623b15fefff
