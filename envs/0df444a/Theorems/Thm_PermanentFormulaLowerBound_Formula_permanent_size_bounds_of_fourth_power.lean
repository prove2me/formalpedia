-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_permanent_size_bounds_of_fourth_power
-- name    : PermanentFormulaLowerBound.Formula.permanent_size_bounds_of_fourth_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/585f0339-a3d4-4a0d-bfa4-28119878c534
-- title:
--   PermanentFormulaLowerBound.Formula.permanent_size_bounds_of_fourth_power
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula

theorem PermanentFormulaLowerBound.Formula.permanent_size_bounds_of_fourth_power
    {n : ℕ} (hn : 32 ≤ n)
    (f : Formula (Fin n × Fin n) ℂ)
    (hfour : n ^ 4 ≤
      32 * (2 * Nat.clog 2 n) * variableLeaves f) :
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (256 * Real.logb 2 (n : ℝ)) ≤
        (internalGateCount f : ℝ) := by sorry
