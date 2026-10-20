-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_variance_le
-- name    : TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/c9a2080f-ea01-40a5-911d-f1e328004a03
-- title:
--   TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_le
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by sorry
