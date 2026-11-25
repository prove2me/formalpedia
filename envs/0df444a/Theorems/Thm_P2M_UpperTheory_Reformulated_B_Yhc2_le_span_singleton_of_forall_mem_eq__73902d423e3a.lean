-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a
-- name    : P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:39.943921+00:00
-- url     : https://prove2.me/theorems/e6c30231-6848-4ab8-852a-8ff4defe7e88
-- title:
--   P2 M Upper Theory Reformulated B Yhc2 le span singleton of forall mem eq  73902d423e3a: P2 M Upper Theory Reformulated B Yhc2 le span singleton of forall mem eq  73902d423e3a
-- statement:
--   The P2 M Upper Theory Reformulated B Yhc2 le span singleton of forall mem eq  73902d423e3a construction uses the P2 M Upper Theory Reformulated B Yhc2 le span singleton of forall mem eq  73902d423e3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeSpanSingletonOfForallMemEq.lean#L3-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeSpanSingletonOfForallMemEq.lean#L3-L44

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by sorry

alias «UpperTheory».«Reformulated».«B».«Yhc2».«le_span_singleton_of_forall_mem_eq».«» := P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a
