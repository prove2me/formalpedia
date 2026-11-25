-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_exists_prime_gt_dvd_eval_of_natDegree_pos
-- name    : UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_prime_gt_dvd_eval_of_natDegree_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:39.139548+00:00
-- url     : https://prove2.me/theorems/8742792c-173a-4e25-af5f-cc8380cf7ab4
-- title:
--   Large Prime Divisors: exists prime gt dvd eval of nat Degree pos
-- statement:
--   The Large Prime Divisors construction uses the exists prime gt dvd eval of nat Degree pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L38-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L38-L95

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_LargePrimeDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.LargePrimeDivisors
open scoped Int LT OfNat Polynomial Dvd

theorem UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_prime_gt_dvd_eval_of_natDegree_pos (f : Polynomial ℤ) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ (p : ℤ) ∣ Polynomial.eval m f := by sorry
