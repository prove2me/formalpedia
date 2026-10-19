-- Prove2me | Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
-- name    : QuantumParallelRepetition.directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/7378dc82-9390-44b7-bb37-5c26aa4be181
-- title:
--   QuantumParallelRepetition.directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
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

theorem QuantumParallelRepetition.directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (target : EuclideanSpace ℂ (s × u))
    (work : EuclideanSpace ℂ (t × v))
    (selected :
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv eA eB) z =
          unconditionalMatchedVerifierTensor target work) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB)
          x y)) z =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s × u) (𝕜 := ℂ)
            (directDSVActualLocalPOVMWinningEffect G PA PB x y))
          target := by sorry
