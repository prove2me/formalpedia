-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_variance_eq
-- name    : TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/393bc356-308e-4ae0-a4a9-e4881cfd836a
-- title:
--   TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_eq
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 := by sorry
