-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_lemma_16
-- name    : SuperactivatedCheating.StateConversion.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:14.091131+00:00
-- url     : https://prove2.me/theorems/c150b1a7-29d5-40e7-9f65-9299394e7e75
-- title:
--   Lemma 16 (used in the proof of Theorem 34) — Choi/Bell affine value identities
-- statement:
--   Let $N$ be any CPTP channel on finite nonzero registers, let $d_a$ be its input dimension and let $M\ge1$. The Definition 15 Choi/Bell construction gives a valid single-round game $G_{\rm par}(N,M)$ satisfying
--   $$\omega^*(G_{\rm par})=1-\frac{1-\omega^*(G_{\rm seq})}{d_a^2},\qquad
--   \omega(G_{\rm par})=1-\frac{1-\omega(G_{\rm seq})}{d_a^2}.$$
--   Both sequential values use the Definition 13 protocol with the same channel and message count. The referee accepts unconditionally outside the canonical Bell outcome, and checks the message only on that outcome. These exact affine identities support Theorem 34.
--
--   Differences from the source:
--   - encoding: the Definition 15 Choi/Bell quantum game → a fixed referee-purified Kraus/Choi construction with its validity asserted; reason: purification and coherent classical sampling preserve every strategy probability; no conclusion is assumed
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: arbitrary finite private registers with prior shared entanglement → Fin-indexed private registers and a unit shared pure state; reason: every finite shared resource admits such a basis and mixed resources admit a local purification; no bound on the dimensions is introduced
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Lemma 16, p. 18.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_EntangledGames

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Lemma 16, p.18: the actual Choi/Bell construction and both affine identities.
The input dimension, not output dimension or message count, occurs squared. -/
theorem lemma_16 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Map A B) (hN : QAlgorithms.IsChannel N) (m : ℕ) (hm : 0 < m) :
    IsQuantumGame (gpar N hN m) ∧
    1 - (1 - (gseq (M := Fin m) N).entangledValue) / (Fintype.card A : ℝ)^2 =
      entangledValue (gpar N hN m) ∧
    1 - (1 - (gseq (M := Fin m) N).localValue) / (Fintype.card A : ℝ)^2 =
      SuperactivatedCheating.StateConversion.localValue (gpar N hN m) := by sorry

end SuperactivatedCheating.StateConversion.Supplement
