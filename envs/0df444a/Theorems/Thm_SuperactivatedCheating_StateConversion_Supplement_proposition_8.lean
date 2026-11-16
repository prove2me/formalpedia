-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_proposition_8
-- name    : SuperactivatedCheating.StateConversion.Supplement.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:12.020823+00:00
-- url     : https://prove2.me/theorems/2e31506a-1b0b-4f4b-b724-80214fd304be
-- title:
--   Proposition 8 (used in the proof of Theorem 34) — entangled-value monotonicity
-- statement:
--   For any two valid finite single-round quantum games $G_1,G_2$, with possibly different question, answer and referee dimensions, the regrouped tensor product is a valid game and
--   $$\omega^*(G_1\times G_2)\le\omega^*(G_1),\qquad\omega^*(G_1\times G_2)\le\omega^*(G_2).$$
--   The entangled values are suprema over arbitrary finite prior pure entanglement and local CPTP maps. No attainment or uniform bound on private dimensions is assumed. This monotonicity supports Theorem 34.
--
--   Differences from the source:
--   - encoding: product of single-round games and both entangled-value inequalities → published game model with a binary product whose validity is part of the conclusion; reason: canonical regrouping preserves both question states and accepting projections; entanglement ranges over all finite dimensions
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: arbitrary finite private registers with prior shared entanglement → Fin-indexed private registers and a unit shared pure state; reason: every finite shared resource admits such a basis and mixed resources admit a local purification; no bound on the dimensions is introduced
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Proposition 8, p. 14.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_EntangledGames

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Proposition 8, p.14: both inequalities, arbitrary distinct games. -/
theorem proposition_8 {A B R a b A' B' R' a' b' : Type}
    [Fintype A] [Fintype B] [Fintype R] [Fintype a] [Fintype b]
    [Fintype A'] [Fintype B'] [Fintype R'] [Fintype a'] [Fintype b']
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq a] [DecidableEq b]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq R'] [DecidableEq a'] [DecidableEq b']
    (G : QuantumGame A B R a b) (H : QuantumGame A' B' R' a' b')
    (hG : IsQuantumGame G) (hH : IsQuantumGame H) :
    IsQuantumGame (gameProd G H) ∧
    entangledValue (gameProd G H) ≤ entangledValue G ∧
    entangledValue (gameProd G H) ≤ entangledValue H := by sorry

end SuperactivatedCheating.StateConversion.Supplement
