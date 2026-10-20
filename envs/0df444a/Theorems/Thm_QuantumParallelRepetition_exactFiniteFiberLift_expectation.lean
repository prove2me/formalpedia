-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFiniteFiberLift_expectation
-- name    : QuantumParallelRepetition.exactFiniteFiberLift_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/3ae7ff9c-7671-4b2d-8690-f20f9fc0800c
-- title:
--   QuantumParallelRepetition.exactFiniteFiberLift_expectation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]

theorem QuantumParallelRepetition.exactFiniteFiberLift_expectation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (value : T → ℝ) :
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T, target point * value point := by sorry
