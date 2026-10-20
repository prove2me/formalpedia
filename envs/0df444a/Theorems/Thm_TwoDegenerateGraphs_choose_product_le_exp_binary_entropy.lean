-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_choose_product_le_exp_binary_entropy
-- name    : TwoDegenerateGraphs.choose_product_le_exp_binary_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/2851e916-c550-48a3-9345-226eca12f06c
-- title:
--   TwoDegenerateGraphs.choose_product_le_exp_binary_entropy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.choose_product_le_exp_binary_entropy
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by sorry
