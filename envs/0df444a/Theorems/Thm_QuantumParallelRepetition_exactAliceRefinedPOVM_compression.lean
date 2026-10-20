-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceRefinedPOVM_compression
-- name    : QuantumParallelRepetition.exactAliceRefinedPOVM_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/83d8efc2-d039-4ff0-93a9-505c49e1655b
-- title:
--   QuantumParallelRepetition.exactAliceRefinedPOVM_compression
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactAliceRefinedPOVM_compression
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) (a : A) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      (exactAliceRefinedPOVM G n S D r a₀ x).effect a *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceCoordinateFilter
        G n S D r.seed r.history r.aliceAnswer x a := by sorry
