-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfQuestionWeight_le_constantStrategy
-- name    : QuantumParallelRepetition.pdfQuestionWeight_le_constantStrategy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/bd2cfade-6a55-41c3-be68-53a424f09fa5
-- title:
--   QuantumParallelRepetition.pdfQuestionWeight_le_constantStrategy
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

theorem QuantumParallelRepetition.pdfQuestionWeight_le_constantStrategy
    (G : Game X Y A B)
    (x : X) (y : Y) (a : A) (b : B)
    (accepted : G.predicate x y a b = true) :
    G.questionWeight x y ≤
      (pdfConstantStrategy G a b).winProbability := by sorry
