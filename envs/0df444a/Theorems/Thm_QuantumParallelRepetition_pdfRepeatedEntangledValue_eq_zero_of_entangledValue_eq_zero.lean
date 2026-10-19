-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
-- name    : QuantumParallelRepetition.pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/5513f8f8-6051-4f8f-9a4c-dbbbdbe878e1
-- title:
--   QuantumParallelRepetition.pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    {n : ℕ} (positive : 0 < n) :
    repeatedEntangledValue G n = 0 := by sorry
