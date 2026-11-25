-- Prove2me | Theorems.Thm_Reformulated_AutPerF_factorial_mul_dp
-- name    : Reformulated.AutPerF.factorial_mul_dp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:13.441148+00:00
-- url     : https://prove2.me/theorems/e030c14e-a5e7-4d46-bb2c-8432e0be7163
-- title:
--   Aut Per F: factorial mul dp
-- statement:
--   The Aut Per F construction uses the factorial mul dp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L40-L42

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]

theorem Reformulated.AutPerF.factorial_mul_dp (m : ℕ) (x : B) : (m ! : B) * dp m x = x ^ m := by sorry
