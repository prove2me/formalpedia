-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk30_hwv_lowering_span_lower__82e8da0c3531
-- name    : P2M_UpperTheory_Reformulated_B_Qk30_hwv_lowering_span_lower__82e8da0c3531
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:41.131153+00:00
-- url     : https://prove2.me/theorems/9dd91ef4-ea15-5d7e-a7d1-5c4b0e20d61a
-- title:
--   P2 M Upper Theory Reformulated B Qk30 hwv lowering span lower  82e8da0c3531: P2 M Upper Theory Reformulated B Qk30 hwv lowering span lower  82e8da0c3531
-- statement:
--   The P2 M Upper Theory Reformulated B Qk30 hwv lowering span lower  82e8da0c3531 construction uses the P2 M Upper Theory Reformulated B Qk30 hwv lowering span lower  82e8da0c3531 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HwvLoweringSpanLower.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HwvLoweringSpanLower.lean#L58-L77

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HwvLoweringSpanLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qk30_hwv_lowering_span_lower__82e8da0c3531.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n},
      b < a → ∀ {x : V}, x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu := by sorry

alias «UpperTheory».«Reformulated».«B».«Qk30».«hwv_lowering_span_lower» := P2M_UpperTheory_Reformulated_B_Qk30_hwv_lowering_span_lower__82e8da0c3531
