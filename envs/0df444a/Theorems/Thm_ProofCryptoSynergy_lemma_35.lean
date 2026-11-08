-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_35
-- name    : ProofCryptoSynergy.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:49.160362+00:00
-- url     : https://prove2.me/theorems/e320ba2b-66b6-4ae1-85da-06ee5b5867c9
-- title:
--   Lemma 35 — WE and $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$ give $\mathsf{NP}\not\subseteq\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$ and $\text{promise-BPP}\subseteq\text{promise-QP}$
-- statement:
--   Assume that subexponentially secure witness encryption exists for SAT and that $\mathsf{coNP}\not\subseteq\mathsf{io\text-NP}$, or that there is no infinitely-often subexponentially optimal proof system. Then
--   $$\mathsf{NP}\not\subseteq\mathsf{io\text-SIZE}[2^{n^{o(1)}}],\quad\text{and}\quad \text{promise-BPP}\subseteq\text{promise-QP}.$$
--
--   The second conclusion is the derandomization that lets the NIWI verifier of Lemma 16 become deterministic in item 1 of Corollary 45.
--
--   Differences from the source:
--   - generalization: hypothesis 2 is coNP ⊄ io-NP → hypothesis 2 is coNP ⊄ io-NP or no infinitely-often subexponentially optimal proof system; reason: the left disjunct specializes to the printed lemma; Corollary 45's proof applies the lemma under the right disjunct, which the printed proof supports through Theorem 10
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - reading: a subexponential function has p(n) ≤ 2^{n^{1/c}} for every c ≥ 1 → for each c ≥ 1, eventually s(n) ≤ 2^{n^{1/c}}; reason: read pointwise the printed clause forces p(n) ≤ 2; the o(1) in the same sentence is asymptotic. This is the stronger conclusion
--   - encoding: promise-P, promise-BPP, promise-QP (used, not defined) → the standard definitions on disjoint pairs of yes- and no-instances, error 1/3; reason: the paper does not define them
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: nondeterministic machine with at most one accepting path; UTIME[n^{polylog(n)}] → deterministic checker on (w, y), |y| ≤ T(|w|), unique accepted y; T(n) = nᵏ + k, resp. 2^{(log₂(n+2))^k}; reason: unique accepting paths correspond to unique witnesses; the two forms of the bounds define the same classes
--   - encoding: coNP ⊄ io-NP (used, not defined) → some L with Lᶜ ∈ NP is not in io-NP, where io-NP means agreeing with a language in NP at infinitely many lengths; reason: the standard definition
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 35, p.31 (PDF 33)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_SubexpWEForSATExists
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_InIoSubexpSIZE
import Definitions.Def_ProofCryptoSynergy_promiseBPP

namespace ProofCryptoSynergy

/-- **Lemma 35** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.31 (PDF 33)). If subexponentially secure WE exists for SAT and `coNP ⊄ io-NP`, then
`NP ⊄ io-SIZE[2^{n^{o(1)}}]` and `promise-BPP ⊆ promise-QP`.

**Formalization Note** Hypothesis 2 is the disjunction of `coNP ⊄ io-NP` and the no-optimal-proof-system assumption. The left disjunct is the
printed lemma; the right is what Corollary 45's proof (p.38) needs, and Lemma 35's proof only uses that its proof system fails to prove some
`ψ_n` for almost all `n`, which Theorem 10 gives. -/
theorem lemma_35 :
    SubexpWEForSATExists → (CoNPNotIoNP ∨ NoIoSubexpOptimalPPS) →
      (∃ L, InNP L ∧ ¬ InIoSubexpSIZE L) ∧ promiseBPP ⊆ promiseQP := by sorry

end ProofCryptoSynergy
