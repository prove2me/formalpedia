-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_sqrt_one_add_le
-- name    : TwoDegenerateGraphs.sqrt_one_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/da9c5056-d64c-4095-a03d-237064ccba55
-- title:
--   TwoDegenerateGraphs.sqrt_one_add_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by sorry
