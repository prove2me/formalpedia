-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_retainedVertex_card_le_manuscriptVertexCount
-- name    : TwoDegenerateGraphs.retainedVertex_card_le_manuscriptVertexCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/3243ad90-5d1a-492d-ab07-329c4f373593
-- title:
--   TwoDegenerateGraphs.retainedVertex_card_le_manuscriptVertexCount
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical

theorem TwoDegenerateGraphs.retainedVertex_card_le_manuscriptVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ manuscriptVertexCount dimension := by sorry
