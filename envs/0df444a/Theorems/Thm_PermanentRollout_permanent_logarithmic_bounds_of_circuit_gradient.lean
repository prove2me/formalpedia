-- Prove2me | Theorems.Thm_PermanentRollout_permanent_logarithmic_bounds_of_circuit_gradient
-- name    : PermanentRollout.permanent_logarithmic_bounds_of_circuit_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/6d26498c-2bbe-44d2-88d8-f61a9e126ed4
-- title:
--   PermanentRollout.permanent_logarithmic_bounds_of_circuit_gradient
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

theorem PermanentRollout.permanent_logarithmic_bounds_of_circuit_gradient
    (hgradient : ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ circuit : ArithmeticCircuit (Fin n × Fin n),
        circuit.polynomial = permanent n →
          (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
            3 * (circuit.size : ℝ)) :
    ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuitComplexity (permanent n) : ℝ) := by sorry
