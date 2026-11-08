-- Prove2me | Theorems.Thm_ProofCryptoSynergy_remark_37
-- name    : ProofCryptoSynergy.remark_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:53.252949+00:00
-- url     : https://prove2.me/theorems/7e2bb06b-710c-423f-9e8b-2bf690de803e
-- title:
--   Remark 37 (first clause) — subexponentially secure iO gives subexponentially secure WE for SAT
-- statement:
--   If subexponentially secure indistinguishability obfuscation exists, then subexponentially secure witness encryption exists for SAT:
--   $$\text{subexponentially secure } i\mathcal O\implies \text{subexponentially secure WE for SAT}.$$
--
--   This is the construction of [Gar+16], cited. It lets Lemmas 35 and 36 start from iO. The remark's second clause, replacing item 1 of those lemmas, is the composition with them and needs no separate statement.
--
--   Differences from the source:
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
--   - encoding: |C₁| = |C₂| ≤ poly(λ) in Definition 12 → equal gate counts ≤ p(λ), the number n of inputs not bounded; reason: an obfuscator in the paper's sense run at the parameter max(λ, n) is one in the Lean sense and conversely, so whether a subexponentially secure iO exists is unchanged
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Remark 37, p.33 (PDF 35)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_SubexpWEForSATExists

namespace ProofCryptoSynergy

/-- **Remark 37, first clause** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.33 (PDF 35); [Gar+16], cited). Subexponentially secure witness encryption for SAT follows from
subexponentially secure iO. -/
theorem remark_37 : SubexpIOExists → SubexpWEForSATExists := by sorry

end ProofCryptoSynergy
