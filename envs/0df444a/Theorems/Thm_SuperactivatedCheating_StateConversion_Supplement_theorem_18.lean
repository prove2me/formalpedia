-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_18
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:56.340047+00:00
-- url     : https://prove2.me/theorems/65473051-c346-4ec3-9a5d-ebe78144dabb
-- title:
--   Theorem 18 (companion theorem; not used in the proof of the goal) — quantum channel–protocol equivalences
-- statement:
--   Let $N$ be any finite-dimensional CPTP channel with nonzero input and output registers and $M\ge1$. The Definition 17 protocol samples an unknown Haar-uniform pure state in $\mathbb C^M$ and accepts the SWAP test against Bob’s decoded state. Then
--   $$H_{\rm seq}(N,M)\text{ has a perfect finite-dimensional assisted strategy}\iff Q_{0,E}^{(1)}(N)\ge\log_2 M,$$
--   $$\omega(H_{\rm seq}(N,M))=1\iff Q_0^{(1)}(N)\ge\log_2 M.$$
--   The circuit is valid, and for every strategy its acceptance trace equals the Haar expectation of its SWAP success. Encoders and decoders are fixed CPTP maps; exact quantum codes recover every density operator, not just a basis. This is the quantum transmission analogue of Theorem 14.
--
--   Differences from the source:
--   - encoding: uniform pure-state sampling and SWAP verification → averaged Haar preparation with explicit equality of its success to the Haar expectation and a verified circuit; reason: linearity preserves every acceptance probability; no sampled classical description is supplied to the encoder
--   - encoding: nonnegative one-shot capacities → complete nonnegative extended-real suprema over all positive achievable dimensions; reason: this preserves the operational capacities and includes M = 1 without undefined logarithms
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
--   - encoding: verifier sampling with private classical information or retained verification copies → the averaged initial density with a retained message or copy register, and local CPTP strategies on the received quantum registers; reason: averaging and a referee-held purification preserve all acceptance probabilities; the sampled classical description is not supplied in Hseq
--   - encoding: a quantum code subspace of dimension M with exact recovery → an M-dimensional register with exact recovery on all its density operators; reason: a choice of orthonormal basis identifies every source code subspace with this register
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 18, p. 19.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 18, p.19. Haar statistics and validity are construction obligations,
not hypotheses. The strategy encoder has no access to the classical description of ψ. -/
theorem theorem_18 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Map A B) (hN : QAlgorithms.IsChannel N) (m : ℕ) (hm : 0 < m) :
    (hseq N m).Valid ∧
    (∀ S : (hseq N m).Strategy, (hseq N m).win S = hseqHaarWin S) ∧
    ((hseq N m).perfect ↔ bitValue m ≤ QE1 N) ∧
    ((hseq N m).localValue = 1 ↔ bitValue m ≤ Q1 N) := by sorry

end SuperactivatedCheating.StateConversion.Supplement
