-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_sq
-- name    : TwoDegenerateGraphs.hammingRetainedVertexCount_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/98bee5c8-7f65-4109-a004-9ccd95d35429
-- title:
--   TwoDegenerateGraphs.hammingRetainedVertexCount_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical

theorem TwoDegenerateGraphs.hammingRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by sorry
