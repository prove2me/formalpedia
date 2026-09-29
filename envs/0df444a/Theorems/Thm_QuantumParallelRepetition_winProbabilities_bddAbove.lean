-- Prove2me | Theorems.Thm_QuantumParallelRepetition_winProbabilities_bddAbove
-- name    : QuantumParallelRepetition.winProbabilities_bddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:55:24.981254+00:00
-- url     : https://prove2.me/theorems/c08be900-e70d-4d2b-af7a-12240faaf349
-- title:
--   The achievable winning probabilities are bounded above
-- statement:
--   The set of winning probabilities achievable by finite-dimensional entangled strategies for a fixed game $G$,
--
--   $$\{\,\omega(S) \;:\; S \text{ an entangled strategy for } G\,\} \subseteq \mathbb{R} ,$$
--
--   is bounded above, with $1$ an explicit upper bound.
--
--   Boundedness is exactly the side condition that the order-theoretic supremum over the reals needs in order to behave: it is what lets `le_csSup` and `csSup_le` be applied to the entangled value, and without it the supremum defining $\omega^{*}(G)$ would carry no information.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L223-L228

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.winProbabilities_bddAbove (G : Game X Y A B) :
    BddAbove (Set.range (Strategy.winProbability (G := G))) := by sorry
