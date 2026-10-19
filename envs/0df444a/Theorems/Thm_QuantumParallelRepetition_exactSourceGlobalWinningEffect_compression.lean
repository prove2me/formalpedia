-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalWinningEffect_compression
-- name    : QuantumParallelRepetition.exactSourceGlobalWinningEffect_compression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/41e0454f-0149-4e22-9d09-c9f4f09bf0d4
-- title:
--   QuantumParallelRepetition.exactSourceGlobalWinningEffect_compression
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourceGlobalWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactSourceGlobalWinningEffect G n S D a₀ b₀ x y
      (exactSourceGlobalJointBasis G n S D r i)
      (exactSourceGlobalJointBasis G n S D r j) =
      exactSourceWinningEffect G n S D r a₀ b₀ x y i j := by sorry
