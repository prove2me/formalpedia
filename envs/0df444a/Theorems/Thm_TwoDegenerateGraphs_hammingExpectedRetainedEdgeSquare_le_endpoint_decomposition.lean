-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
-- name    : TwoDegenerateGraphs.hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/99568e18-8fa5-419f-b1ba-f368ab9a54d3
-- title:
--   TwoDegenerateGraphs.hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 := by sorry
