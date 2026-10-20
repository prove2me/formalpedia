-- Prove2me | Theorems.Thm_SpherePacking_harmonicDimension_choose_bounds
-- name    : SpherePacking.harmonicDimension_choose_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:35.827193+00:00
-- url     : https://prove2.me/theorems/99e7a892-2e82-4981-b87a-92b1590cc9c3
-- title:
--   SpherePacking.harmonicDimension_choose_bounds
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

theorem SpherePacking.harmonicDimension_choose_bounds
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (n + k - 2).choose k ≤ Gegenbauer.harmonicDimension n k ∧
      Gegenbauer.harmonicDimension n k ≤ 2 * (n + k - 2).choose k := by sorry
