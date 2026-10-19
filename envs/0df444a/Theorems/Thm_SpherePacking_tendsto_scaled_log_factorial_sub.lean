-- Prove2me | Theorems.Thm_SpherePacking_tendsto_scaled_log_factorial_sub
-- name    : SpherePacking.tendsto_scaled_log_factorial_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/f36efbc5-a488-4892-888a-1ce5bafccf12
-- title:
--   SpherePacking.tendsto_scaled_log_factorial_sub
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

theorem SpherePacking.tendsto_scaled_log_factorial_sub
    (k : ℕ → ℕ) (u : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hu : u ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))
      atTop (nhds (u * Real.log u - u)) := by sorry
