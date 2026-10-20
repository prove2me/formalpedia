-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
-- name    : TwoDegenerateGraphs.abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/4a04f6bc-ac92-4ebb-ab45-744a06826d8f
-- title:
--   TwoDegenerateGraphs.abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by sorry
