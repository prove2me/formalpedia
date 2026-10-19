-- Prove2me | Theorems.Thm_PermanentRollout_logarithmic_lower_bound_of_gradient
-- name    : PermanentRollout.logarithmic_lower_bound_of_gradient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/0c128ba2-6e36-4dc6-96dd-d3530a57ae38
-- title:
--   PermanentRollout.logarithmic_lower_bound_of_gradient
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.logarithmic_lower_bound_of_gradient {n d q : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hgradient : (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
      3 * (q : ℝ)) :
    (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤ (q : ℝ) := by sorry
