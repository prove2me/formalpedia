-- Prove2me | Theorems.Thm_ProofCryptoSynergy_theorem_39
-- name    : ProofCryptoSynergy.theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:37.079481+00:00
-- url     : https://prove2.me/theorems/277800c1-f78e-4a44-8daf-0c5950f52a00
-- title:
--   Theorem 39 — conditional construction of certifiable keyed OWPs from keyed OWPs
-- statement:
--   Assume that there exist a subexponentially secure keyed OWP and a subexponentially secure NIWI, and that there is no infinitely-often subexponentially optimal proof system. Then there exists a subexponentially secure certifiable keyed OWP.
--
--   Certifying that a key defines a permutation is what the obvious use of iO-based permutations lacks. The proof-complexity assumption supplies it by way of the NIWI.
--
--   Differences from the source:
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 39, p.34 (PDF 36)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_NIWIScheme
import Definitions.Def_ProofCryptoSynergy_KeyedOWP

namespace ProofCryptoSynergy

/-- **Theorem 39** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.34 (PDF 36)). If there exist a subexponentially secure keyed OWP and a subexponentially secure NIWI, and there is no
infinitely-often subexponentially optimal proof system, then there exists a subexponentially secure certifiable keyed OWP. -/
theorem theorem_39 :
    SubexpKeyedOWPExists → SubexpNIWIExists → NoIoSubexpOptimalPPS →
      SubexpCertKeyedOWPExists := by sorry

end ProofCryptoSynergy
