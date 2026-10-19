-- Prove2me | Theorems.Thm_QuantumParallelRepetition_conditionedCoordinateEffects_born_expansion
-- name    : QuantumParallelRepetition.conditionedCoordinateEffects_born_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/744456fc-9be2-4cb3-bf91-d69fd1432a64
-- title:
--   QuantumParallelRepetition.conditionedCoordinateEffects_born_expansion
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.conditionedCoordinateEffects_born_expansion
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (i : Fin n) (a : A) (b : B) :
    bornTracePairing S.state.matrix
        (conditionedAliceCoordinateEffect G n S D α xs i a)
        (conditionedBobCoordinateEffect G n S D β ys i b) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if (∀ (j : Fin n) (hj : j ∈ D), aa j = α ⟨j, hj⟩) ∧
          aa i = a then
          if (∀ (j : Fin n) (hj : j ∈ D), bb j = β ⟨j, hj⟩) ∧
            bb i = b then S.outcomeProbability xs ys aa bb else 0
        else 0 := by sorry
