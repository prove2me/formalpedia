-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_sub
-- name    : TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/8d6d6dac-e3cc-4acd-9ad4-0316e0003b7f
-- title:
--   TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_sub
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_sub
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount)
    (f : Bool → Bool → ℝ) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right) =
      (((oneCount : ℝ) / (parentCount : ℝ)) *
        (1 - (oneCount : ℝ) / (parentCount : ℝ)) /
          ((parentCount : ℝ) - 1)) *
        (f false true + f true false - f false false - f true true) := by sorry
