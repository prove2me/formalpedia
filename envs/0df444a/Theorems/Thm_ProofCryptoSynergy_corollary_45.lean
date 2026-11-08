-- Prove2me | Theorems.Thm_ProofCryptoSynergy_corollary_45
-- name    : ProofCryptoSynergy.corollary_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:44.752129+00:00
-- url     : https://prove2.me/theorems/e72a7345-5b6d-42d0-86d7-10573b74c384
-- title:
--   Corollary 45 — circuit lower bounds for $\mathsf{UP}\cap\mathsf{coUP}$ from $i\mathcal O$ and proof complexity
-- statement:
--   Assume that there exists a subexponentially secure indistinguishability obfuscator and that there is no infinitely-often subexponentially optimal proof system. Then:
--   1. there is a language $L$ with $L,L^c\in\mathsf{UTIME}[n^{\mathrm{polylog}(n)}]$ and $L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$;
--   2. if $\text{promise-P}=\text{promise-BPP}$, there is a language $L$ with $L,L^c\in\mathsf{UP}$ and $L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$.
--
--   Here $L\notin\mathsf{io\text-SIZE}[2^{n^{o(1)}}]$ means that for every subexponential $s$, for all but finitely many $n$, $L$ on $\{0,1\}^n$ has no circuit of size at most $s(n)$.
--
--   This is the formal version of the paper's Theorem 1, an almost-everywhere lower bound in a small class that a black-box reduction cannot give [BDV17].
--
--   Differences from the source:
--   - reading: inverse subexponential ε(λ) in Definitions 12, 13 → ∀ polynomial size bound p, ∃ δ > 0, size 2^{λ^δ} and advantage 2^{−λ^δ}, for all large λ; reason: the form the paper's proofs use (Definitions 14, 18, Lemma 22, Lemma 32, proof of Theorem 64); §2.1's literal form would give security only below every 2^{n^δ}
--   - reading: a subexponential function has p(n) ≤ 2^{n^{1/c}} for every c ≥ 1 → for each c ≥ 1, eventually s(n) ≤ 2^{n^{1/c}}; reason: read pointwise the printed clause forces p(n) ≤ 2; the o(1) in the same sentence is asymptotic. This is the stronger conclusion
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: L-size(x) ≤ p(L′-size(x)), with value ∞ if there is no proof; constants c ≥ 1 → every L′-proof π′ of x yields an L-proof π with |π| ≤ 2^{|π′|^{1/c}}; c a positive integer; reason: the same condition, since p is increasing and decreases in c
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: nondeterministic machine with at most one accepting path; UTIME[n^{polylog(n)}] → deterministic checker on (w, y), |y| ≤ T(|w|), unique accepted y; T(n) = nᵏ + k, resp. 2^{(log₂(n+2))^k}; reason: unique accepting paths correspond to unique witnesses; the two forms of the bounds define the same classes
--   - encoding: promise-P, promise-BPP, promise-QP (used, not defined) → the standard definitions on disjoint pairs of yes- and no-instances, error 1/3; reason: the paper does not define them
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
--   - encoding: |C₁| = |C₂| ≤ poly(λ) in Definition 12 → equal gate counts ≤ p(λ), the number n of inputs not bounded; reason: an obfuscator in the paper's sense run at the parameter max(λ, n) is one in the Lean sense and conversely, so whether a subexponentially secure iO exists is unchanged
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Corollary 45, p.38 (PDF 40)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_InIoSubexpSIZE
import Definitions.Def_ProofCryptoSynergy_promiseBPP

namespace ProofCryptoSynergy

/-- **Corollary 45** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.38 (PDF 40)). Assume that there exists a subexponentially secure iO and that there is no infinitely-often subexponentially optimal
proof system. Then
1. `UTIME[n^{polylog(n)}] ∩ coUTIME[n^{polylog(n)}] ⊄ io-SIZE[2^{n^{o(1)}}]`;
2. if promise-P = promise-BPP, then `UP ∩ coUP ⊄ io-SIZE[2^{n^{o(1)}}]`.

**Formalization Note** In each clause one language `L` lies in the class, its complement lies in the class, and for every subexponential `s`, for all but
finitely many `n`, `L` on `{0,1}ⁿ` has no circuit of size at most `s(n)`. -/
theorem corollary_45 :
    SubexpIOExists → NoIoSubexpOptimalPPS →
      (∃ L, InQuasiU L ∧ InQuasiU Lᶜ ∧ ¬ InIoSubexpSIZE L) ∧
      (promiseP = promiseBPP → ∃ L, InUP L ∧ InUP Lᶜ ∧ ¬ InIoSubexpSIZE L) := by sorry

end ProofCryptoSynergy
