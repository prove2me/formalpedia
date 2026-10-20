-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingBall_card_entropy_lower
-- name    : TwoDegenerateGraphs.manuscriptHammingBall_card_entropy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/5d681013-710e-4c3c-8676-21e8d5e5bc54
-- title:
--   TwoDegenerateGraphs.manuscriptHammingBall_card_entropy_lower
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.manuscriptHammingBall_card_entropy_lower
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by sorry
