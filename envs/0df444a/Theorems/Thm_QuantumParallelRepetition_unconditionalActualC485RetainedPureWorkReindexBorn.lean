-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485RetainedPureWorkReindexBorn
-- name    : QuantumParallelRepetition.unconditionalActualC485RetainedPureWorkReindexBorn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/03c2e812-2a83-4d99-b88b-96429fa6e913
-- title:
--   QuantumParallelRepetition.unconditionalActualC485RetainedPureWorkReindexBorn
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualC485RetainedPureWorkReindexBorn
    {s t v : Type}
    [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    [Fintype v] [DecidableEq v]
    (e : t ≃ v)
    (winning : Matrix s s ℂ)
    (z : EuclideanSpace ℂ (s × t)) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix t t ℂ))) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × v) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix v v ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr (Equiv.refl s) e) z) := by sorry
