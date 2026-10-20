-- Prove2me | Theorems.Thm_PermanentRollout_permanent_circuit_loglog_bigOmega
-- name    : PermanentRollout.permanent_circuit_loglog_bigOmega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/d733c2c7-0fa3-4a5a-bbd3-3700b0db21a6
-- title:
--   PermanentRollout.permanent_circuit_loglog_bigOmega
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open scoped LinearAlgebra.Projectivization

theorem PermanentRollout.permanent_circuit_loglog_bigOmega :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
        (circuitComplexity (permanent n) : ℝ) := by sorry
