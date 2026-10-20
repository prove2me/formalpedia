-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
-- name    : QuantumParallelRepetition.unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/09a52450-0574-4157-87b6-cb84a1ba8b20
-- title:
--   QuantumParallelRepetition.unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
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
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (left right : DecidableEq τ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance left U V z =
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance right U V z := by sorry
