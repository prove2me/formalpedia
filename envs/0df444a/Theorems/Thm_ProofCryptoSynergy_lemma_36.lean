-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_36
-- name    : ProofCryptoSynergy.lemma_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:36.042193+00:00
-- url     : https://prove2.me/theorems/4c2f76fd-8772-476a-90e2-82796d51b201
-- title:
--   Lemma 36 — WE and $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$ give subexponentially secure one-way functions
-- statement:
--   Assume that subexponentially secure witness encryption exists for SAT and that $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$, or that there is no infinitely-often subexponentially optimal proof system. Then subexponentially secure one-way functions exist.
--
--   It is the first step of the proof of Corollary 45, supplying the one-way functions for Lemma 15.
--
--   Differences from the source:
--   - generalization: hypothesis 2 is coNP ⊄ io-NP → hypothesis 2 is coNP ⊄ io-NP or no infinitely-often subexponentially optimal proof system; reason: the left disjunct specializes to the printed lemma; Corollary 45's proof applies the lemma under the right disjunct, which the printed proof supports through Theorem 10
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - encoding: one-way function (used, not defined) → the format of Definition 18: ∃ δ > 0, nonuniform adversaries; reason: the paper does not define it
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: coNP ⊄ io-NP (used, not defined) → some L with Lᶜ ∈ NP is not in io-NP, where io-NP means agreeing with a language in NP at infinitely many lengths; reason: the standard definition
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 36, p.33 (PDF 35)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_SubexpWEForSATExists
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_SubexpOWFExists

namespace ProofCryptoSynergy

/-- **Lemma 36** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.33 (PDF 35)). If subexponentially secure WE exists for SAT and `coNP ⊄ io-NP`, then subexponentially secure
one-way functions exist.

**Formalization Note** Hypothesis 2 is the same disjunction as in `lemma_35`; the left disjunct is the printed lemma. -/
theorem lemma_36 :
    SubexpWEForSATExists → (CoNPNotIoNP ∨ NoIoSubexpOptimalPPS) → SubexpOWFExists := by sorry

end ProofCryptoSynergy
