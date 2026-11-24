-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yoa4_add_gap_le
-- name    : UpperTheory.Reformulated.B.Yoa4.add_gap_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:27.625579+00:00
-- url     : https://prove2.me/theorems/8ee34f7f-edf5-4b9e-8552-e1aea18e6c8c
-- title:
--   Yoa4: add gap le
-- statement:
--   The Yoa4 construction uses the add gap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AddGapLe.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AddGapLe.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yoa4.add_gap_le :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by sorry
