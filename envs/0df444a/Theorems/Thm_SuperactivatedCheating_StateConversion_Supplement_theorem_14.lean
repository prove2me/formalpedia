-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_14
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:57.868697+00:00
-- url     : https://prove2.me/theorems/574de710-72ed-4992-a54a-2863bb5a77b5
-- title:
--   Theorem 14 (companion theorem; not used in the proof of the goal) — classical channel–protocol equivalences
-- statement:
--   Let $N$ be any CPTP channel between finite nonzero registers and let $M\ge1$. For the canonical classical-message protocol of Definition 13,
--   $$G_{\rm seq}(N,M)\text{ has a perfect finite-dimensional assisted strategy}\iff C_{0,E}^{(1)}(N)\ge\log_2 M,$$
--   $$\omega(G_{\rm seq}(N,M))=1\iff C_0^{(1)}(N)\ge\log_2 M.$$
--   The constructed circuit is valid. The first clause asserts an attained perfect strategy; the second uses the supremum over all unassisted strategies. This identifies exact classical transmission with perfect protocol execution.
--
--   Differences from the source:
--   - encoding: positive message counts and finite-dimensional channels → finite registers, M ≥ 1, canonical valid Gseq circuit; capacities in ℝ≥0∞; reason: these represent every source channel and message alphabet; log₂ M is nonnegative
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
--   - encoding: verifier sampling with private classical information or retained verification copies → the averaged initial density with a retained message or copy register, and local CPTP strategies on the received quantum registers; reason: averaging and a referee-held purification preserve all acceptance probabilities; the sampled classical description is not supplied in Hseq
--   - encoding: Bob measures a decoding POVM and sends a classical outcome → Bob returns a message register measured diagonally by the verifier; reason: a channel followed by this diagonal measurement realizes exactly the same arbitrary finite-outcome POVMs
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 14, p. 17.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 14, p.17, canonical Definition 13 protocol; both clauses. -/
theorem theorem_14 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Map A B) (hN : QAlgorithms.IsChannel N) (m : ℕ) (hm : 0 < m) :
    (gseq (M := Fin m) N).Valid ∧
    ((gseq (M := Fin m) N).perfect ↔ bitValue m ≤ CE1 N) ∧
    ((gseq (M := Fin m) N).localValue = 1 ↔ bitValue m ≤ C1 N) := by sorry

end SuperactivatedCheating.StateConversion.Supplement
