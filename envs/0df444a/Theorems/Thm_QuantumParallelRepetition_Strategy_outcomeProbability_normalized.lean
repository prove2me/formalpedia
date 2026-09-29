-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_outcomeProbability_normalized
-- name    : QuantumParallelRepetition.Strategy.outcomeProbability_normalized
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:51:14.717885+00:00
-- url     : https://prove2.me/theorems/c7655505-cd3f-43a9-abf9-c16ff5e6dc3b
-- title:
--   Born-rule outcome probabilities sum to one
-- statement:
--   For every question pair $(x,y)$ the answer distribution produced by an entangled strategy is normalised:
--
--   $$\sum_{a \in A} \sum_{b \in B} \Pr[a,b \mid x,y] \;=\; 1 .$$
--
--   Linearity of the trace moves the sum inside, completeness of the joint measurement replaces it by the identity, and the trace of the shared state is one because it is a density matrix.
--
--   With nonnegativity this completes the statement that a strategy induces a bona fide probability distribution on answer pairs, which is what licenses bounding the winning probability by one.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L162-L173

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.outcomeProbability_normalized
    (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) = 1 := by sorry
