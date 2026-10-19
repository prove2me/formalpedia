-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfPredicate_not_accepted_of_entangledValue_eq_zero
-- name    : QuantumParallelRepetition.pdfPredicate_not_accepted_of_entangledValue_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/faf2a381-0cf7-41da-8ae5-a2506155a746
-- title:
--   QuantumParallelRepetition.pdfPredicate_not_accepted_of_entangledValue_eq_zero
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

theorem QuantumParallelRepetition.pdfPredicate_not_accepted_of_entangledValue_eq_zero
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    (x : X) (y : Y) (a : A) (b : B)
    (supported : 0 < G.questionWeight x y) :
    G.predicate x y a b ≠ true := by sorry
