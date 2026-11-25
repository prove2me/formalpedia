-- Prove2me | Theorems.Thm_UpperTheory_integralClosure_finite
-- name    : UpperTheory.integralClosure_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:44.860794+00:00
-- url     : https://prove2.me/theorems/62a5868f-dc88-4017-999a-56c735653554
-- title:
--   Upper Theory: integral Closure finite
-- statement:
--   The Upper Theory construction uses the integral Closure finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FiniteOfFiniteOverNormal.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FiniteOfFiniteOverNormal.lean#L28-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteOfFiniteOverNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory
open nonZeroDivisors

theorem UpperTheory.integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by sorry
