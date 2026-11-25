-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_second
-- name    : UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_second
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:53.300448+00:00
-- url     : https://prove2.me/theorems/ecaada13-3ff8-4aee-9428-0562d35ab729
-- title:
--   r26a: double sum reduce second
-- statement:
--   The r26a construction uses the double sum reduce second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L81-L92

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r26a
open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

theorem UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_second {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε c then E a d * E c a else 0) := by sorry
