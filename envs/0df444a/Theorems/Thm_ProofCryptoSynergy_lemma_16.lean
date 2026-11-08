-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_16
-- name    : ProofCryptoSynergy.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:05.732631+00:00
-- url     : https://prove2.me/theorems/409eb936-6618-4a10-88ed-a81b3f1e69a6
-- title:
--   Lemma 16 — iO and trapdoor permutations give NIWIs with randomized verifiers
-- statement:
--   If subexponentially secure iO exists and subexponentially secure full-domain trapdoor one-way permutations exist, then there is a pair of randomized polynomial-time algorithms $(P,V)$ such that:
--   1. **completeness**: if $\varphi(w)=1$ then for all $\lambda$, $\Pr_{P,V}[V(\varphi,P(\varphi,w,1^\lambda),1^\lambda)=1]=1$;
--   2. **negligible soundness error**: there is a negligible $\mu$ such that for all $\lambda$, unsatisfiable $\varphi$ with $|\varphi|\le\lambda$ and $\pi$, $\Pr_V[V(\varphi,\pi,1^\lambda)=1]\le\mu(\lambda)$;
--   3. **witness indistinguishability**: for some $\varepsilon(\lambda)=2^{-\lambda^{\Omega(1)}}$, if $\varphi(w)=\varphi(w')=1$ then for all $\lambda$, $P(\varphi,w,1^\lambda)\approx_{\varepsilon(\lambda)}P(\varphi,w',1^\lambda)$.
--
--   This is a result of [BP15], cited, in its subexponential and trapdoor form. Derandomizing its verifier gives the NIWI used by Theorem 39.
--
--   Differences from the source:
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: |C₁| = |C₂| ≤ poly(λ) in Definition 12 → equal gate counts ≤ p(λ), the number n of inputs not bounded; reason: an obfuscator in the paper's sense run at the parameter max(λ, n) is one in the Lean sense and conversely, so whether a subexponentially secure iO exists is unchanged
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 16, p.21 (PDF 23)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_KeyedOWP
import Definitions.Def_ProofCryptoSynergy_SubexpRandNIWIExists

namespace ProofCryptoSynergy

/-- **Lemma 16** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.21 (PDF 23); [BP15], cited). If subexponentially secure iO exists and subexponentially secure full-domain trapdoor one-way
permutations exist, then there exist subexponentially secure NIWIs with randomized verifiers and negligible soundness error. -/
theorem lemma_16 : SubexpIOExists → SubexpTDPExists → SubexpRandNIWIExists := by sorry

end ProofCryptoSynergy
