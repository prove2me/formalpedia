-- Prove2me | Theorems.Thm_QuantumParallelRepetition_repeatedEntangledValue_relabel
-- name    : QuantumParallelRepetition.repeatedEntangledValue_relabel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:10:12.612884+00:00
-- url     : https://prove2.me/theorems/a4316ac9-0b53-47b5-81e9-9eaecf7a1dc1
-- title:
--   Relabelling commutes with parallel repetition
-- statement:
--   A relabelling of the alphabets of a game induces a relabelling of every parallel repetition of it, coordinatewise. Consequently the repeated entangled values agree for every number of repetitions:
--
--   $$\omega^*(H^n) = \omega^*(G^n) \qquad \text{for all } n.$$
--
--   In the $n$-fold repetition the referee samples the coordinates independently and accepts only if every coordinate accepts, so the product weight and the conjunction of predicates each transform coordinatewise under the induced equivalence of tuples.
-- source:
--   Prove2me bridge for openai/ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs — universe transport, not part of the upstream development (which states parallel repetition for alphabets in `Type` only).

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem QuantumParallelRepetition.repeatedEntangledValue_relabel
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (hw : ∀ x y, H.questionWeight (eX x) (eY y) = G.questionWeight x y)
    (hp : ∀ x y a b, H.predicate (eX x) (eY y) (eA a) (eB b) = G.predicate x y a b)
    (n : ℕ) :
    repeatedEntangledValue H n = repeatedEntangledValue G n := by sorry
