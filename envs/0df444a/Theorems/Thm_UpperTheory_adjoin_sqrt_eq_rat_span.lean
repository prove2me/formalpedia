-- Prove2me | Theorems.Thm_UpperTheory_adjoin_sqrt_eq_rat_span
-- name    : UpperTheory.adjoin_sqrt_eq_rat_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:49.606367+00:00
-- url     : https://prove2.me/theorems/932cb05f-c5bf-4912-8b54-6563aa7d16f5
-- title:
--   Upper Theory: adjoin sqrt eq rat span
-- statement:
--   The Upper Theory construction uses the adjoin sqrt eq rat span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdjoinSqrtEqRatSpan.lean#L3-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdjoinSqrtEqRatSpan.lean#L3-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AdjoinSqrtEqRatSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.adjoin_sqrt_eq_rat_span :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), s ^ 2 = -(d : E) → ∀ x : E, x ∈ IntermediateField.adjoin ℚ ({s} : Set E) → ∃ a b : ℚ, x = (a : E) + (b : E) * s := by sorry
