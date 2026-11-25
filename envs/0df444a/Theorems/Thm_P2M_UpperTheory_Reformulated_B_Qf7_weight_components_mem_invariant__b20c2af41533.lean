-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf7_weight_components_mem_invariant__b20c2af41533
-- name    : P2M_UpperTheory_Reformulated_B_Qf7_weight_components_mem_invariant__b20c2af41533
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:38.159656+00:00
-- url     : https://prove2.me/theorems/7e3336bb-f59e-4cb9-bd28-e3fa24ae57e0
-- title:
--   P2 M Upper Theory Reformulated B Qf7 weight components mem invariant  b20c2af41533: P2 M Upper Theory Reformulated B Qf7 weight components mem invariant  b20c2af41533
-- statement:
--   The P2 M Upper Theory Reformulated B Qf7 weight components mem invariant  b20c2af41533 construction uses the P2 M Upper Theory Reformulated B Qf7 weight components mem invariant  b20c2af41533 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WeightComponentsMemInvariant.lean#L34-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WeightComponentsMemInvariant.lean#L34-L67

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightComponentsMemInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qf7_weight_components_mem_invariant__b20c2af41533.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      [CharZero K] (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (W : Submodule K V),
      (∀ (a : Fin n), ∀ x ∈ W, (E a a : V → V) x ∈ W) →
        ∀ (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
          (∀ mu ∈ s, f mu ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) → ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W := by sorry

alias «UpperTheory».«Reformulated».«B».«Qf7».«weight_components_mem_invariant» := P2M_UpperTheory_Reformulated_B_Qf7_weight_components_mem_invariant__b20c2af41533
