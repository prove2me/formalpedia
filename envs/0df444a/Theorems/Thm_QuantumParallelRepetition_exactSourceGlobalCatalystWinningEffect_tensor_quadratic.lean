-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalCatalystWinningEffect_tensor_quadratic
-- name    : QuantumParallelRepetition.exactSourceGlobalCatalystWinningEffect_tensor_quadratic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/5907e7d7-3af6-4d3c-8a68-b14351186b1d
-- title:
--   QuantumParallelRepetition.exactSourceGlobalCatalystWinningEffect_tensor_quadratic
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
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (tensorEmbezzlementTarget (n := e)
        (exactGlobalHistoryFinPsi G n S D r x y)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)) := by sorry
