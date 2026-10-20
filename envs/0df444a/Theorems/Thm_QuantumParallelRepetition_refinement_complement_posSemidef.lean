-- Prove2me | Theorems.Thm_QuantumParallelRepetition_refinement_complement_posSemidef
-- name    : QuantumParallelRepetition.refinement_complement_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/bea9efc9-b58d-4785-9db8-fc0097e2ea28
-- title:
--   QuantumParallelRepetition.refinement_complement_posSemidef
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.refinement_complement_posSemidef
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    ((∑ b : ι, effect b) - effect a).PosSemidef := by sorry
