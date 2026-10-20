-- Prove2me | Theorems.Thm_PermanentRollout_permanent_circuit_gradient_bound
-- name    : PermanentRollout.permanent_circuit_gradient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/4c86fbf1-5ca2-48e6-b4d9-ef4c12e4b353
-- title:
--   PermanentRollout.permanent_circuit_gradient_bound
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

theorem PermanentRollout.permanent_circuit_gradient_bound
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n) :
    (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
      3 * (circuit.size : ℝ) := by sorry
