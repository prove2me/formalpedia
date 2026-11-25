-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_mul_sub_mul_add_ne_zero
-- name    : UpperTheory.Reformulated.B.P6.LargePrimeDivisors.mul_sub_mul_add_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:24.089307+00:00
-- url     : https://prove2.me/theorems/9e5f7812-6c97-5bfe-afd3-23488cb67ddb
-- title:
--   Large Prime Divisors: mul sub mul add ne zero
-- statement:
--   The Large Prime Divisors construction uses the mul sub mul add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L8-L23

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
open Polynomial

theorem UpperTheory.Reformulated.B.P6.LargePrimeDivisors.mul_sub_mul_add_ne_zero (f : Polynomial ℤ) (hf : 0 < f.natDegree) (c : ℤ) :
    f * (f - C c) * (f + C c) ≠ 0 := by sorry
