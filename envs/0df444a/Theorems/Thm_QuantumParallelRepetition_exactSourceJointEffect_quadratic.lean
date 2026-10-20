-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceJointEffect_quadratic
-- name    : QuantumParallelRepetition.exactSourceJointEffect_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/501ef6d0-0e05-423d-968e-56435c7c835c
-- title:
--   QuantumParallelRepetition.exactSourceJointEffect_quadratic
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourceJointEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
        (exactSourceJointEffect G n S D r a₀ b₀ x y a b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by sorry
