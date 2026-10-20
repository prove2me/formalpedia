-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceWinningEffect_quadratic_eq_conditional
-- name    : QuantumParallelRepetition.exactSourceWinningEffect_quadratic_eq_conditional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/5951ed2f-c4cd-45ec-a434-dd19e718177e
-- title:
--   QuantumParallelRepetition.exactSourceWinningEffect_quadratic_eq_conditional
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

theorem QuantumParallelRepetition.exactSourceWinningEffect_quadratic_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y := by sorry
