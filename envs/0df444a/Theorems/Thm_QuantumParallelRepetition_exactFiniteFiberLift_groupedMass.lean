-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFiniteFiberLift_groupedMass
-- name    : QuantumParallelRepetition.exactFiniteFiberLift_groupedMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/aa1c76f7-60fa-40f6-bf88-2251a7a38bc3
-- title:
--   QuantumParallelRepetition.exactFiniteFiberLift_groupedMass
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
omit [Fintype T]

theorem QuantumParallelRepetition.exactFiniteFiberLift_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (exactFiniteFiberLift projection original target) point =
        target point := by sorry
