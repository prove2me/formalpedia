-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620
-- name    : P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:20:55.688802+00:00
-- url     : https://prove2.me/theorems/cee2a0dc-ffd5-5b72-9f7a-a64e558fdc9c
-- title:
--   P2 M Upper Theory Reformulated B Finite Place Sum Bound finite Place sum le  f64df29d0620: P2 M Upper Theory Reformulated B Finite Place Sum Bound finite Place sum le  f64df29d0620
-- statement:
--   The P2 M Upper Theory Reformulated B Finite Place Sum Bound finite Place sum le  f64df29d0620 construction uses the P2 M Upper Theory Reformulated B Finite Place Sum Bound finite Place sum le  f64df29d0620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FinitePlaceSumLe.lean#L3-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FinitePlaceSumLe.lean#L3-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitePlaceSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620.{u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberField.FinitePlace K) {α : Type u_2} (s : Finset α)
      (f : α → K) {B : ℝ}, (0 : ℝ) ≤ B → (∀ a ∈ s, (v : K → ℝ) (f a) ≤ B) → (v : K → ℝ) (∑ a ∈ s, f a) ≤ B := by sorry

alias «UpperTheory».«Reformulated».«B».«FinitePlaceSumBound».«finitePlace_sum_le».«» := P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620
