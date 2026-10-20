-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_le_one
-- name    : TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/38cd5203-788f-479a-9e3a-40997955a560
-- title:
--   TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_le_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_le_one
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by sorry
