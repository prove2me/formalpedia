-- Prove2me | Theorems.Thm_UpperTheory_closure_span_coefficients
-- name    : UpperTheory.closure_span_coefficients
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:52.214798+00:00
-- url     : https://prove2.me/theorems/acf4d3c4-bc46-47b3-8b56-2bece56849bd
-- title:
--   Upper Theory: closure span coefficients
-- statement:
--   The Upper Theory construction uses the closure span coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ClosureSpanCoefficients.lean#L3-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ClosureSpanCoefficients.lean#L3-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureSpanCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.closure_span_coefficients :
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by sorry
