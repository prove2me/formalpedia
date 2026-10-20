-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_norm_le_one
-- name    : QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_norm_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/2bc052ef-812b-4e69-b64d-cc491e48f865
-- title:
--   QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_norm_le_one
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

theorem QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_norm_le_one
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef)
    (complement : (1 - effect).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ))‖ ≤ 1 := by sorry
