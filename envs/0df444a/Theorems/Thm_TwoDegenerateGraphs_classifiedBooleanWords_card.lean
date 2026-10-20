-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_classifiedBooleanWords_card
-- name    : TwoDegenerateGraphs.classifiedBooleanWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/4b122f81-5f3a-4996-bd05-763da0f026e0
-- title:
--   TwoDegenerateGraphs.classifiedBooleanWords_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.classifiedBooleanWords_card
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by sorry
