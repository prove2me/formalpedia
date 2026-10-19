-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualRetainedPOVM_ext
-- name    : QuantumParallelRepetition.unconditionalActualRetainedPOVM_ext
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/f3bd15ce-8e16-4d2f-9cb0-a22d17e34be3
-- title:
--   QuantumParallelRepetition.unconditionalActualRetainedPOVM_ext
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualRetainedPOVM_ext
    {C ι : Type*} [Fintype C] [Fintype ι] [DecidableEq ι]
    (P Q : POVM C ι)
    (same : ∀ (a : C) (i j : ι), P.effect a i j = Q.effect a i j) :
    P = Q := by sorry
