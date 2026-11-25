-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_third
-- name    : UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_third
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:05.209801+00:00
-- url     : https://prove2.me/theorems/a0b85825-7616-4d49-831d-61e276a2d872
-- title:
--   r26a: double sum reduce third
-- statement:
--   The r26a construction uses the double sum reduce third property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L68-L79

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

theorem UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_third {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by sorry
