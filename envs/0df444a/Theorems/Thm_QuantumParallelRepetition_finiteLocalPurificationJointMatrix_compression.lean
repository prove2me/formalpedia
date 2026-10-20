-- Prove2me | Theorems.Thm_QuantumParallelRepetition_finiteLocalPurificationJointMatrix_compression
-- name    : QuantumParallelRepetition.finiteLocalPurificationJointMatrix_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/64a4686a-9b25-483a-ae23-057196b9babb
-- title:
--   QuantumParallelRepetition.finiteLocalPurificationJointMatrix_compression
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

theorem QuantumParallelRepetition.finiteLocalPurificationJointMatrix_compression
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        (((EA ⊗ₖ
            (1 : Matrix (S.Alice × S.Bob)
              (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)) *
        finiteLocalPurificationJointMatrix S KA KB =
      (((KA.conjTranspose * EA * KA) ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * EB * KB)) := by sorry
