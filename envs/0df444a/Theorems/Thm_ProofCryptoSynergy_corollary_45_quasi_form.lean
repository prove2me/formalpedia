-- Prove2me | Theorems.Thm_ProofCryptoSynergy_corollary_45_quasi_form
-- name    : ProofCryptoSynergy.corollary_45_quasi_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:04.849293+00:00
-- url     : https://prove2.me/theorems/46ed472a-4d14-4208-ae33-c5919fea80b0
-- title:
--   Proof of Corollary 45, p.38 — quasipolynomial verifier gives $\mathsf{UTIME}[n^{\mathrm{polylog}(n)}]\cap\mathsf{coUTIME}[n^{\mathrm{polylog}(n)}]$
-- statement:
--   Assume that there exist a subexponentially secure keyed OWP and a subexponentially secure NIWI with a deterministic quasipolynomial-time verifier, and that there is no infinitely-often subexponentially optimal proof system. Then there is one language $L$ with $L,L^c\in\mathsf{UTIME}[n^{\mathrm{polylog}(n)}]$ and
--   $$L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}].$$
--
--   This is the unnumbered step on which item 1 of Corollary 45 rests: certification takes quasipolynomial rather than polynomial time, and the circuit lower bound holds as is.
--
--   Differences from the source:
--   - reading: a subexponential function has p(n) ≤ 2^{n^{1/c}} for every c ≥ 1 → for each c ≥ 1, eventually s(n) ≤ 2^{n^{1/c}}; reason: read pointwise the printed clause forces p(n) ≤ 2; the o(1) in the same sentence is asymptotic. This is the stronger conclusion
--   - encoding: nondeterministic machine with at most one accepting path; UTIME[n^{polylog(n)}] → deterministic checker on (w, y), |y| ≤ T(|w|), unique accepted y; T(n) = nᵏ + k, resp. 2^{(log₂(n+2))^k}; reason: unique accepting paths correspond to unique witnesses; the two forms of the bounds define the same classes
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of Corollary 45, second paragraph, p.38 (PDF 40)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_NIWIScheme
import Definitions.Def_ProofCryptoSynergy_KeyedOWP
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_InIoSubexpSIZE

namespace ProofCryptoSynergy

/-- **Proof of Corollary 45, second paragraph** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.38 (PDF 40)). A subexponentially secure keyed OWP, a subexponentially secure NIWI with a
deterministic quasipolynomial-time verifier, and no infinitely-often subexponentially optimal proof system give a language `L` with `L` and its complement
in `UTIME[n^{polylog(n)}]` and `L ∉ io-SIZE[2^{n^{o(1)}}]`. -/
theorem corollary_45_quasi_form :
    SubexpKeyedOWPExists → SubexpQuasiNIWIExists → NoIoSubexpOptimalPPS →
      ∃ L, InQuasiU L ∧ InQuasiU Lᶜ ∧ ¬ InIoSubexpSIZE L := by sorry

end ProofCryptoSynergy
