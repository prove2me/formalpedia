-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeVariance_le
-- name    : TwoDegenerateGraphs.hammingExpectedRetainedEdgeVariance_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/24ce4841-0696-4a42-b318-35903ccba575
-- title:
--   TwoDegenerateGraphs.hammingExpectedRetainedEdgeVariance_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingExpectedRetainedEdgeVariance_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by sorry
