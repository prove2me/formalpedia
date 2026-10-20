-- Prove2me | Theorems.Thm_SpherePacking_factorialLogError_eq
-- name    : SpherePacking.factorialLogError_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/46a7e523-e48e-4895-bab2-c1e62bb1c81e
-- title:
--   SpherePacking.factorialLogError_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology

theorem SpherePacking.factorialLogError_eq (n : ℕ) (hn : n ≠ 0) :
    factorialLogError n =
      Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ) := by sorry
