-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unitaryConjugatePOVM_jointEffect
-- name    : QuantumParallelRepetition.unitaryConjugatePOVM_jointEffect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/0724c211-e60d-471b-809e-141579bc53e6
-- title:
--   QuantumParallelRepetition.unitaryConjugatePOVM_jointEffect
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
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unitaryConjugatePOVM_jointEffect
    {A B d : Type} [Fintype A] [Fintype B]
    [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ)
    (P : POVM A d) (Q : POVM B d)
    (a : A) (b : B) :
    (unitaryConjugatePOVM U P).effect a ⊗ₖ
      (unitaryConjugatePOVM V Q).effect b =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))) := by sorry
