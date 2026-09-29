-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_le_one
-- name    : QuantumParallelRepetition.entangledValue_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:57:05.614374+00:00
-- url     : https://prove2.me/theorems/37cf10e8-5287-483b-b615-e3414f123f6b
-- title:
--   The entangled value of a game is at most one
-- statement:
--   The entangled value of a finite two-player game is at most one:
--
--   $$\omega^{*}(G) \;=\; \sup_{S} \omega(S) \;\le\; 1 .$$
--
--   Every achievable winning probability is at most one, so the supremum is too; when no strategy exists the real supremum of the empty set is $0 \le 1$.
--
--   Together with nonnegativity this places the entangled value in $[0,1]$, which is what makes the hypothesis $\omega^{*}(G) < 1$ of the parallel-repetition theorem a statement about a genuine gap below the trivial upper bound.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L230-L239

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.entangledValue_le_one (G : Game X Y A B) :
    entangledValue G ≤ 1 := by sorry
