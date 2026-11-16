-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_32
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:25:13.884203+00:00
-- url     : https://prove2.me/theorems/1c6d0ec7-978c-4305-a331-b71666483963
-- title:
--   Theorem 32 (companion theorem; not used in the proof of the goal) — quantum-message superactivation
-- statement:
--   There exist finite nonzero channel registers, a CPTP channel $N$ between them and a positive integer $M$ such that the valid Definition 17 quantum-message protocol satisfies
--   $$\omega(H_{\rm seq}(N,M))<1,\qquad\forall n\ge2,\quad\omega(H_{\rm seq}(N,M)^n)=1.$$
--   One channel and one message dimension work for every $n$. Repetition samples independent Haar input states and accepts the product of the SWAP tests; encoders and decoders may act jointly across copies. This preserves the specific quantum-message family in the source and its full repetition claim.
--
--   Differences from the source:
--   - encoding: a class of Definition 17 protocols, one witness for every n ≥ 2 → existence of a finite channel and positive message dimension in the exact Hseq family; reason: specifies the source family without restricting the channel or message dimension; independent SWAP tests define repetitions
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
--   - encoding: trace winning probabilities and local or assisted supremum values → real parts of accepting traces and real suprema over actual strategies; reason: on valid circuits the traces are real probabilities; the strategy sets are nonempty and bounded in [0,1], so no default supremum is used
--   - encoding: finite-dimensional prior shared states and local private resources → unit pure shared states and arbitrary finite retained memories; local resources are product pure states; reason: mixed resources can be purified locally without changing probabilities; every private dimension is represented by Fin e, and shared randomization cannot improve a supremum
--   - encoding: verifier sampling with private classical information or retained verification copies → the averaged initial density with a retained message or copy register, and local CPTP strategies on the received quantum registers; reason: averaging and a referee-held purification preserve all acceptance probabilities; the sampled classical description is not supplied in Hseq
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 32, p. 25.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 32, p.25: one fixed Definition 17 witness, every n ≥ 2.
Parallel repetition uses independent Haar questions and a product of SWAP acceptors. -/
theorem theorem_32 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    ∃ N : Map (Fin a) (Fin b), QAlgorithms.IsChannel N ∧
    ∃ m : ℕ, 0 < m ∧ (hseq N m).Valid ∧ (hseq N m).localValue < 1 ∧
      ∀ n : ℕ, 2 ≤ n → ((hseq N m).rep n).localValue = 1 := by sorry

end SuperactivatedCheating.StateConversion.Supplement
