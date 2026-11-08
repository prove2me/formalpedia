-- Prove2me | Theorems.Thm_ProofCryptoSynergy_proposition_20
-- name    : ProofCryptoSynergy.proposition_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:37.816755+00:00
-- url     : https://prove2.me/theorems/a030d7a9-be3d-4027-b0d2-e25067da403c
-- title:
--   Proposition 20 — certifiable keyed OWPs give $\mathsf{UP}\cap\mathsf{coUP}\not\subseteq\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$
-- statement:
--   If there exists a subexponentially secure certifiable keyed OWP, then there is one language $L$ with $L,L^c\in\mathsf{UP}$ and
--   $$L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}].$$
--
--   This is the folklore step from a certifiable permutation to unambiguous hardness: inverting bits of the permutation is in $\mathsf{UP}\cap\mathsf{coUP}$.
--
--   **Formalization Note** The conclusion is at all input lengths; the language of the printed proof is hard only at lengths $n(\eta)$, so it has to be padded, and the statement is unchanged.
--
--   Differences from the source:
--   - reading: a subexponential function has p(n) ≤ 2^{n^{1/c}} for every c ≥ 1 → for each c ≥ 1, eventually s(n) ≤ 2^{n^{1/c}}; reason: read pointwise the printed clause forces p(n) ≤ 2; the o(1) in the same sentence is asymptotic. This is the stronger conclusion
--   - encoding: nondeterministic machine with at most one accepting path; UTIME[n^{polylog(n)}] → deterministic checker on (w, y), |y| ≤ T(|w|), unique accepted y; T(n) = nᵏ + k, resp. 2^{(log₂(n+2))^k}; reason: unique accepting paths correspond to unique witnesses; the two forms of the bounds define the same classes
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Proposition 20, p.22 (PDF 24)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_KeyedOWP
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_InIoSubexpSIZE

namespace ProofCryptoSynergy

/-- **Proposition 20** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.22 (PDF 24); folklore). If there exists a subexponentially secure certifiable keyed OWP, then
`UP ∩ coUP ⊄ io-SIZE[2^{n^{o(1)}}]`.

**Formalization Note** One language `L` with `L` and its complement in UP. The hardness is at all input lengths: the language built in the printed proof
lives on lengths `n(η)` and has to be padded, which leaves the statement unchanged. -/
theorem proposition_20 :
    SubexpCertKeyedOWPExists → ∃ L, InUP L ∧ InUP Lᶜ ∧ ¬ InIoSubexpSIZE L := by sorry

end ProofCryptoSynergy
