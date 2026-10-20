-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateBobBasisOverlap_sum
-- name    : QuantumParallelRepetition.unconditionalConjugateBobBasisOverlap_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/e2c884d6-cf9a-4545-b332-f0413021cf18
-- title:
--   QuantumParallelRepetition.unconditionalConjugateBobBasisOverlap_sum
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

theorem QuantumParallelRepetition.unconditionalConjugateBobBasisOverlap_sum
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i b : Fin d) :
    (∑ j : Fin d,
      unitaryBasisOverlap U V i j *
        star ((V : Matrix (Fin d) (Fin d) ℂ) b j)) =
      star ((U : Matrix (Fin d) (Fin d) ℂ) b i) := by sorry
