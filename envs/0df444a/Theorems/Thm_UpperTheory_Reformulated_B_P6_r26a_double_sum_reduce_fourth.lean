-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_fourth
-- name    : UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_fourth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:49.031109+00:00
-- url     : https://prove2.me/theorems/f9db6f59-0c28-4e00-8139-a302a0024a2a
-- title:
--   r26a: double sum reduce fourth
-- statement:
--   The r26a construction uses the double sum reduce fourth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L53-L66

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

theorem UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_fourth {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by sorry
