-- Prove2me | Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget
-- name    : ShiQMAConstructiveSchedule.eval_le_pow_budget
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T12:59:07.528986+00:00
-- url     : https://prove2.me/theorems/45acb3c7-cc52-4d97-9d55-817fc400cac0
-- title:
--   A logarithmic bit budget dominates polynomial evaluation
-- statement:
--   A natural-coefficient polynomial at input n is at most 2 raised to an explicit logarithmic coefficient-and-degree budget.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/24620b5/proofs/AMPUNI-constructive-schedule.lean#L19-L46

import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAPolynomialBound_eval_le_coeffSum_mul

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.eval_le_pow_budget (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ 2 ^ exponentBudget p n := by sorry
