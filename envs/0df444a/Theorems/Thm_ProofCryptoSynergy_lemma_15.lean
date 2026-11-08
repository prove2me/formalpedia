-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_15
-- name    : ProofCryptoSynergy.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:09.709768+00:00
-- url     : https://prove2.me/theorems/45e71067-278d-4012-869f-2dae23974bd8
-- title:
--   Lemma 15 — one-way functions and iO give full-domain trapdoor one-way permutations
-- statement:
--   If subexponentially secure one-way functions exist and subexponentially secure iO exists, then subexponentially secure full-domain trapdoor one-way permutations exist.
--
--   This is a result of [SZ25b], cited, in its subexponential form ([SZ25a, Theorem 53]). Full-domain trapdoor permutations are the keyed permutations that Theorem 39 starts from.
--
--   Differences from the source:
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - encoding: full-domain trapdoor one-way permutation (used, not defined) → a keyed OWP with a trapdoor from the same coins and a polynomial-time inverter; reason: standard; p.22 says they are a special case of keyed OWPs
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
--   - encoding: |C₁| = |C₂| ≤ poly(λ) in Definition 12 → equal gate counts ≤ p(λ), the number n of inputs not bounded; reason: an obfuscator in the paper's sense run at the parameter max(λ, n) is one in the Lean sense and conversely, so whether a subexponentially secure iO exists is unchanged
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 15, p.21 (PDF 23)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_SubexpOWFExists
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_KeyedOWP

namespace ProofCryptoSynergy

/-- **Lemma 15** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.21 (PDF 23); [SZ25b], cited). If subexponentially secure one-way functions exist and subexponentially secure iO exists,
then subexponentially secure full-domain trapdoor one-way permutations exist. -/
theorem lemma_15 : SubexpOWFExists → SubexpIOExists → SubexpTDPExists := by sorry

end ProofCryptoSynergy
