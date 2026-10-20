-- Prove2me | Theorems.Thm_QuantumParallelRepetition_convexMixtureStrategy_outcomeProbability
-- name    : QuantumParallelRepetition.convexMixtureStrategy_outcomeProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/3983aa06-2691-461f-a506-272af1594a2b
-- title:
--   QuantumParallelRepetition.convexMixtureStrategy_outcomeProbability
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.convexMixtureStrategy_outcomeProbability
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (convexMixtureStrategy p hp h_normalized S).outcomeProbability
        x y a b =
      ∑ j : J, p j * (S j).outcomeProbability x y a b := by sorry
