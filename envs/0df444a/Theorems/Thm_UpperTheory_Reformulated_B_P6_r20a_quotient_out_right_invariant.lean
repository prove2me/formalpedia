-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r20a_quotient_out_right_invariant
-- name    : UpperTheory.Reformulated.B.P6.r20a.quotient_out_right_invariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:22.173024+00:00
-- url     : https://prove2.me/theorems/4a6c0249-4f87-5579-9084-4c6bc14a1f64
-- title:
--   r20a: quotient out right invariant
-- statement:
--   The r20a construction uses the quotient out right invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a

theorem UpperTheory.Reformulated.B.P6.r20a.quotient_out_right_invariant {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ (x k : H), k ∈ K → u (x * k) = u x) (x : H) :
    u (Quotient.out (x : H ⧸ K)) = u x := by sorry
