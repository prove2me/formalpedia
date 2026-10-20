-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_mono_on_half
-- name    : TwoDegenerateGraphs.binaryEntropy_mono_on_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/a8dcd3b1-cc3b-4bc5-8cea-83a7c2236fb7
-- title:
--   TwoDegenerateGraphs.binaryEntropy_mono_on_half
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.binaryEntropy_mono_on_half
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by sorry
