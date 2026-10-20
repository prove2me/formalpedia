-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/ec9fe300-d8a8-429d-9a4d-f36f40d037bd
-- title:
--   QuantumParallelRepetition.unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
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

theorem QuantumParallelRepetition.unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
    {d : ℕ}
    (winning :
      Matrix (Fin (d * 1) × Fin (d * 1))
        (Fin (d * 1) × Fin (d * 1)) ℂ)
    (ξ : BipartiteUnitVector d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
        (Matrix.reindex
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d)))
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d))) winning))
      (unconditionalConjugatePureVector ξ.val) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ)) := by sorry
