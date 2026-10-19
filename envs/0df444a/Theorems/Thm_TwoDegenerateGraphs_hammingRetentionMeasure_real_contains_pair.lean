-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_pair
-- name    : TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/f8b9dc3e-fc87-4d77-ae8a-58a55901bdee
-- title:
--   TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_pair
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by sorry
