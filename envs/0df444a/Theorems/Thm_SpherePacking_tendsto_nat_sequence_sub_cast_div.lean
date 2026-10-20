-- Prove2me | Theorems.Thm_SpherePacking_tendsto_nat_sequence_sub_cast_div
-- name    : SpherePacking.tendsto_nat_sequence_sub_cast_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:35.827193+00:00
-- url     : https://prove2.me/theorems/75322524-6704-4c80-af65-c6bd52f92d9d
-- title:
--   SpherePacking.tendsto_nat_sequence_sub_cast_div
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology

theorem SpherePacking.tendsto_nat_sequence_sub_cast_div
    (N : ℕ → ℕ) (c : ℕ) (u : ℝ)
    (hN : Tendsto N atTop atTop)
    (hNu : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds u)) :
    Tendsto (fun n : ℕ => ((N n - c : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds u) := by sorry
