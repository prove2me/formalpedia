-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qn14_le_of_add_one_le_succ
-- name    : UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:47.027584+00:00
-- url     : https://prove2.me/theorems/b0c86a11-6dd8-43f6-b3ea-c73a22e9934a
-- title:
--   Qn14: le of add one le succ
-- statement:
--   The Qn14 construction uses the le of add one le succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeOfAddOneLeSucc.lean#L3-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeOfAddOneLeSucc.lean#L3-L24

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by sorry
