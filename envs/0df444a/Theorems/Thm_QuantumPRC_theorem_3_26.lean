-- Prove2me | Theorems.Thm_QuantumPRC_theorem_3_26
-- name    : QuantumPRC.theorem_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:41.033392+00:00
-- url     : https://prove2.me/theorems/112d7962-c729-4def-8660-0417298d3c9a
-- title:
--   Theorem 3.26 (corrected: $m(\lambda)\ge\lambda^\kappa$ eventually) — PRCs robust to $p$-bounded noise from Assumption 5
-- statement:
--   Let $p\in[0,\tfrac12)$. There is a constant $\alpha$ such that the following holds. Let $n,m$ be efficient polynomial lengths with $m(\lambda)\ge\alpha\,n(\lambda)$ for all sufficiently large $\lambda$, and with $m(\lambda)\ge\lambda^\kappa$ for all sufficiently large $\lambda$, for some constant $\kappa>0$. If Assumption 5 holds, then
--
--   1. there is an $(n,m)$ public-key PRC that is robust to every $p$-bounded noise channel, and
--   2. there is an $(n,m)$ secret-key PRC that is robust to every $p$-bounded noise channel.
--
--   Here a PRC (Definitions 3.19, 3.24) has PPT key generation and encoding and deterministic polynomial-time decoding, and satisfies robustness, soundness, and pseudorandomness against quantum adversaries making classical queries. The theorem supplies the classical codes from which the PRFCs, and then the PRICs of the mission, are built.
--
--   Differences from the source:
--   - correction: for polynomials n, m with m(λ) ≥ α·n(λ) for all sufficiently large λ → additionally m(λ) ≥ λ^κ for all sufficiently large λ, for some κ > 0; reason: for n ≡ 1 and a constant m, soundness and a union bound over the 2^m strings give Pr_sk[Dec(sk, c) = ⊥ for all c] → 1, while robustness to the identity channel (0-bounded) needs Dec(sk, Enc(sk, x)) = x with probability → 1; every non-constant polynomial m satisfies the added condition (paper.md decision 6)
--   - generalization: n, m (or nL, nP, ℓ, r, m) are polynomials → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - encoding: robust to p-bounded noise → one scheme that is a PRC robust to E for every classical noise channel E that is p-bounded; reason: the meaning of the phrase; a p-bounded channel is any probabilistic map, as Definition 3.6 allows
--   - reading: Assumption 5 as printed (n^ϵ as a dimension, log without a base in items 3–4, Ω(log² n) and Θ(log n), QPT adversaries for Assumptions 1–4) → n^ϵ is ⌊n^ϵ⌋; log is log₂ in items 3–4 (Real.logb 2; ⌈log n⌉ is ⌈Real.logb 2 n⌉₊); Ω/Θ are eventual bounds with natural log over every function g, t; the adversaries are uniform circuit families indexed by the sample number n that read a prefix of the challenge code; reason: the paper fixes neither a log base (§3.1, p.16) nor a rounding of n^ϵ; log₂ is the base of [Lee26]; Ω/Θ are base-free (paper.md decision 8)
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 3.26, p.24 (restated and proved p.87); Definitions 3.6, 3.19, 3.24; Assumption 5

import Mathlib
import Definitions.Def_QuantumPRC_SKPRC

open Filter

namespace QuantumPRC

/-- **Theorem 3.26** (PRCs from Assumption 5; corrected: `m(λ) ≥ λ^κ` eventually). Hsieh, Yamada,
arXiv:2609.38986 (sha256 6901b59d…), Theorem 3.26, p.24 (restated and proved p.87): "Let `p ∈ [0, 1/2)`.
There exists a constant `α` satisfying the following. For polynomials `n, m : ℕ → ℕ` satisfying
`m(λ) ≥ α · n(λ)` for all sufficiently large `λ`, if Assumption 5 is true, then there exist `(n, m)`
public-key PRCs and `(n, m)` secret-key PRCs robust to `p`-bounded noise."

The added hypothesis `m(λ) ≥ λ^κ` for all sufficiently large `λ`, for some `κ > 0`, holds for every
non-constant polynomial `m`. Without it the statement is false: for `n ≡ 1` and a constant `m`, soundness
(36)/(39) and a union bound over the `2^m` strings give `Pr_sk[Dec(sk, c) = ⊥ for all c] → 1`, while
robustness to the identity channel (which is `0`-bounded) requires `Dec(sk, Enc(sk, x)) = x` with
probability `→ 1`.

**Formalization Note.** "Polynomials" are `EffPoly` lengths. "Robust to `p`-bounded noise" means one
scheme that is a PRC robust to every `p`-bounded channel (Definition 3.6). -/
theorem theorem_3_26 (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    ∃ α : ℝ, ∀ n m : ℕ → ℕ, EffPoly n → EffPoly m →
      (∀ᶠ lam in atTop, α * (n lam : ℝ) ≤ m lam) →
      (∃ κ : ℝ, 0 < κ ∧ ∀ᶠ lam : ℕ in atTop, (lam : ℝ) ^ κ ≤ m lam) →
      Assumption5 →
      (∃ S : PKPRC n m, ∀ E : CNoise m, IsPBounded p E → S.IsPRC E) ∧
      (∃ S : SKPRC n m, ∀ E : CNoise m, IsPBounded p E → S.IsPRC E) := by sorry

end QuantumPRC
