-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_badPairLayerRetentionBound_eq_exp
-- name    : TwoDegenerateGraphs.badPairLayerRetentionBound_eq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/220ea57b-878f-4990-9b31-35026665c2a5
-- title:
--   TwoDegenerateGraphs.badPairLayerRetentionBound_eq_exp
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.badPairLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (midpointBeta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by sorry
