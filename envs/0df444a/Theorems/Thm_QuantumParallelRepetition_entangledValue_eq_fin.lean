-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_eq_fin
-- name    : QuantumParallelRepetition.entangledValue_eq_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:11:46.148782+00:00
-- url     : https://prove2.me/theorems/1eb54a99-5536-4040-a89b-a2344b8fdd1e
-- title:
--   Entangled value is computed by a game on Fin alphabets
-- statement:
--   Every finite game has the same entangled value as a game whose alphabets are standard finite types:
--
--   $$\omega^*(G) = \omega^*\big(G'\big), \qquad G' : \mathrm{Game}\ \mathrm{Fin}\,|X|\ \mathrm{Fin}\,|Y|\ \mathrm{Fin}\,|A|\ \mathrm{Fin}\,|B|.$$
--
--   This is the universe-lowering step. A game over arbitrary finite alphabets lives in whatever universe those alphabets inhabit, while `Fin n` always lives in `Type`. Any statement about entangled values proved for games in `Type` therefore transfers to games over arbitrary finite alphabets.
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

theorem QuantumParallelRepetition.entangledValue_eq_fin (G : Game X Y A B) :
    entangledValue G
      = entangledValue (G.relabel (Fintype.equivFin X) (Fintype.equivFin Y)
          (Fintype.equivFin A) (Fintype.equivFin B)) := by sorry
