-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_double_sum_reduce_first
-- name    : UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_first
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:52.149994+00:00
-- url     : https://prove2.me/theorems/8dacf7b4-9120-4532-a18b-69b2eeebbaec
-- title:
--   r26a: double sum reduce first
-- statement:
--   The r26a construction uses the double sum reduce first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L38-L51

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

theorem UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_first {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by sorry
