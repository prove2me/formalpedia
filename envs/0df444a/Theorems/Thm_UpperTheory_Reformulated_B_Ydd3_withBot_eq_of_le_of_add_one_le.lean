-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Ydd3_withBot_eq_of_le_of_add_one_le
-- name    : UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:57.645217+00:00
-- url     : https://prove2.me/theorems/a0df2a4f-aa75-4f0b-8ad8-3f6ddbade1fe
-- title:
--   Ydd3: with Bot eq of le of add one le
-- statement:
--   The Ydd3 construction uses the with Bot eq of le of add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WithBotEqOfLeOfAddOneLe.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WithBotEqOfLeOfAddOneLe.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by sorry
