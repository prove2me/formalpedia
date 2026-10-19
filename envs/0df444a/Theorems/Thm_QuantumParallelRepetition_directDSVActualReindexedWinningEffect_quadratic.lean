-- Prove2me | Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedWinningEffect_quadratic
-- name    : QuantumParallelRepetition.directDSVActualReindexedWinningEffect_quadratic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/674ea02c-59e6-45d6-849d-772574b0df7f
-- title:
--   QuantumParallelRepetition.directDSVActualReindexedWinningEffect_quadratic
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

theorem QuantumParallelRepetition.directDSVActualReindexedWinningEffect_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (winning : Matrix κ κ ℂ)
    (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (Matrix.reindex e.symm e.symm winning)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e z) := by sorry
