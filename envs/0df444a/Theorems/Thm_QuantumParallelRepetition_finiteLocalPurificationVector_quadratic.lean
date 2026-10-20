-- Prove2me | Theorems.Thm_QuantumParallelRepetition_finiteLocalPurificationVector_quadratic
-- name    : QuantumParallelRepetition.finiteLocalPurificationVector_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/8d3f8d42-6b14-4156-b65d-aa28ccb2a04e
-- title:
--   QuantumParallelRepetition.finiteLocalPurificationVector_quadratic
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.finiteLocalPurificationVector_quadratic
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (eA × (S.Alice × S.Bob)) × eB) (𝕜 := ℂ)
        (((EA ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)))
      (finiteLocalPurificationVector S KA KB) =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * EA * KA)
        (KB.conjTranspose * EB * KB) := by sorry
