-- Prove2me | Theorems.Thm_QuantumPRC_Supplement_theorem_4_7
-- name    : QuantumPRC.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:37:44.200211+00:00
-- url     : https://prove2.me/theorems/c360e673-87b6-4767-a0a0-453896877799
-- title:
--   Theorem 4.7 (corrected: second claim needs $n_L(\lambda)\ge1$ infinitely often) — impossibility of QPRCs with small redundancy
-- statement:
--   Let $n_L\le n_P$ be polynomial lengths (the standing assumption of §4).
--
--   1. Let $t:\mathbb N\to\mathbb N$ satisfy $n_P(\lambda)-n_L(\lambda)<t(\lambda)\le n_P(\lambda)$ for all sufficiently large $\lambda$. Then there is a $t$-local noise family $\mathcal E$ (Definition 3.7) such that **no** keyed code from $n_L$ to $n_P$ qubits is robust to $\mathcal E$, i.e. for every finite key distribution and all CPTP encoders and decoders,
--   $$
--   \Big\|\mathop{\mathbb E}_{\mathsf{sk}}\,\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{sk}}-\mathrm{id}\Big\|_\diamond\le\mathrm{negl}(\lambda)
--   $$
--   fails.
--   2. Let $c$ be a positive integer with $n_P(\lambda)-n_L(\lambda)<c$ for all sufficiently large $\lambda$, and suppose $n_L(\lambda)\ge1$ for infinitely many $\lambda$. Then there is a $c$-local noise family $\mathcal E$ such that no keyed code from $n_L$ to $n_P$ qubits is robust to $\mathcal E$.
--
--   The noise family is chosen before the code. In particular, for every ideal distribution $\mathcal D$, no secret-key $\mathcal D$-QPRC robust to $\mathcal E$ exists; with $c=1$ this shows that QPRCs without redundancy cannot withstand all one-local noise.
--
--   Differences from the source:
--   - generalization: no secret-key D-QPRCs (for an arbitrary ideal distribution D) robust to E exist → no KeyedCode is robust to E: any finite key distribution with real weights and any CPTP Enc_sk, Dec_sk, without efficiency or pseudorandomness; reason: every secret-key D-QPRC is such a code (finitely distributed classical key, CPTP maps) with the same key-averaged channel, so the Lean statement implies the printed one for every D (SUPPLEMENT.md decision 2)
--   - correction: second claim: a positive integer c with nP(λ) − nL(λ) < c for all sufficiently large λ → additionally nL(λ) ≥ 1 for infinitely many λ; reason: counterexample nL ≡ nP ≡ 0, c = 1: every CPTP map on the 1-dimensional space is the identity, so the trivial code is robust to every E (SUPPLEMENT.md decision 3)
--   - generalization: nL, nP are polynomials → nL, nP are EffPoly lengths (polynomially bounded, 1^λ ↦ 1^{n(λ)} polynomial-time) with nL ≤ nP; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (base convention)
--   - encoding: nP(λ) − nL(λ) < t(λ), nP(λ) − nL(λ) < c → nP λ < nL λ + t λ, nP λ < nL λ + c; reason: avoids truncated natural-number subtraction; same instances
--   - encoding: t-local error map E → a family E of WildeQIT.QChannel on nP(λ) qubits with IsLocalNoise t nP E (Definition 3.7); reason: the paper's notion; CPTP maps in finite dimension have Kraus representations
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 4.7, p.27; standing assumption of §4, p.24; Definitions 3.7, 4.3

import Mathlib
import Definitions.Def_QuantumPRC_Supplement_KeyedCode

open Filter

namespace QuantumPRC.Supplement

/-- **Theorem 4.7** (Impossibility of QPRCs with small redundancy; corrected second claim). Hsieh,
Yamada, *Quantum Pseudorandom Error-Correcting Codes*, arXiv:2609.38986 (version of October 29, 2026,
sha256 6901b59d…), Theorem 4.7, p.27: "Let `D` be an arbitrary ideal distribution. Let `t : ℕ → ℕ` be
an arbitrary function satisfying `nP(λ) − nL(λ) < t(λ) ≤ nP(λ)` for all sufficiently large `λ`. Then,
there exists a `t`-local error map `E` such that no secret-key `D`-QPRCs robust to `E` exist. In
addition, if there exists a positive integer `c` such that `nP(λ) − nL(λ) < c` for all sufficiently
large `λ`, there exists a `c`-local error map `E` such that no secret-key `D`-QPRCs robust to `E`
exist." Standing assumption of §4, p.24: `nL, nP` are polynomials with `nL(λ) ≤ nP(λ)`.

**Formalization Note.**
* The impossibility is stated for every `KeyedCode`: any finite key distribution and any CPTP
  encoders and decoders, with no efficiency and no pseudorandomness. Every secret-key `D`-QPRC, for
  every ideal distribution `D`, is such a code, so this implies the printed statement for all `D`.
* `E` is chosen before the code (`∃ E, ∀ S`), and "`t`-local" is Definition 3.7 (`IsLocalNoise`).
* `nP − nL < t` is written `nP < nL + t` (no truncated subtraction).
* Second claim, correction: it also assumes `nL(λ) ≥ 1` for infinitely many `λ`. Without it the
  printed claim is false: for `nL ≡ nP ≡ 0` and `c = 1` every map on the 1-dimensional space is the
  identity, so the trivial code is robust to every `E`.
* "Polynomials" are `EffPoly` lengths, as in the base mission. -/
theorem theorem_4_7 (nL nP : ℕ → ℕ) (hnL : EffPoly nL) (hnP : EffPoly nP)
    (hle : ∀ lam, nL lam ≤ nP lam) :
    (∀ t : ℕ → ℕ, (∀ᶠ lam in atTop, nP lam < nL lam + t lam ∧ t lam ≤ nP lam) →
      ∃ E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam)),
        IsLocalNoise t nP E ∧ ∀ S : KeyedCode nL nP, ¬ S.Robust E) ∧
    (∀ c : ℕ, 0 < c → (∀ᶠ lam in atTop, nP lam < nL lam + c) → (∃ᶠ lam in atTop, 1 ≤ nL lam) →
      ∃ E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam)),
        IsLocalNoise (fun _ => c) nP E ∧ ∀ S : KeyedCode nL nP, ¬ S.Robust E) := by sorry

end QuantumPRC.Supplement
