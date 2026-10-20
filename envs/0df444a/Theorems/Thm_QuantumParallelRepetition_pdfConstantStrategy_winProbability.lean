-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdfConstantStrategy_winProbability
-- name    : QuantumParallelRepetition.pdfConstantStrategy_winProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/d82e9061-aae5-41b1-bf22-1418b381d536
-- title:
--   QuantumParallelRepetition.pdfConstantStrategy_winProbability
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

theorem QuantumParallelRepetition.pdfConstantStrategy_winProbability
    (G : Game X Y A B) (a : A) (b : B) :
    (pdfConstantStrategy G a b).winProbability =
      ∑ x : X, ∑ y : Y,
        if G.predicate x y a b = true then G.questionWeight x y else 0 := by sorry
