-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_jointMeasurementOperator_complete
-- name    : QuantumParallelRepetition.Strategy.jointMeasurementOperator_complete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:50:32.228624+00:00
-- url     : https://prove2.me/theorems/1af7982b-42c4-41c9-b2e0-e60a14b64113
-- title:
--   The joint measurement operators sum to the identity
-- statement:
--   For every question pair $(x,y)$ the joint measurement operators of an entangled strategy form a resolution of the identity:
--
--   $$\sum_{a \in A} \sum_{b \in B} A^{x}_{a} \otimes B^{y}_{b} \;=\; I .$$
--
--   Bilinearity of the Kronecker product lets the double sum be factored as $\left(\sum_a A^{x}_{a}\right) \otimes \left(\sum_b B^{y}_{b}\right)$, and each factor is the identity by POVM completeness; the identity tensored with the identity is the identity on the joint system.
--
--   This is the completeness half of the measurement axioms, and it is what forces the outcome probabilities of a strategy to sum to one.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L147-L160

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.jointMeasurementOperator_complete
    (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.jointMeasurementOperator x y a b) = 1 := by sorry
