-- Prove2me | Theorems.Thm_RevisitXor_claim_1
-- name    : RevisitXor.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:35.162455+00:00
-- url     : https://prove2.me/theorems/0ef129ed-b169-45d1-804c-be8d604ba190
-- title:
--   Claim (1): $\mathbb P_\pi[C_\pi(h)\ge t/M]\le2\cdot2^{-ct}$ for $t\ge c\log M$
-- statement:
--   There are absolute constants $c_1,c_2>0$ such that the following holds. Let $m\ge1$, $M=2^m$, and let $h:[2]^{2m}\to[2]$ be any fixed function. For a uniformly random fixed-point-free involution $\pi$ of $[2]^m$ (a uniformly random perfect matching of the complete graph on $[2]^m$), let $C_\pi(h)=\operatorname{corr}(h,f_\pi)$. Then for every $t\ge c_1\log M$,
--
--   $$\mathbb P_\pi\big[C_\pi(h)\ge t/M\big]\le 2\cdot2^{-c_2t}. \tag{1}$$
--
--   Theorem 1 follows from (1) by a union bound over the functions of $S$ and their complements.
--
--   **Formalization Note** $h$ is read on the pair $(x,y)\in[2]^m\times[2]^m$. The probability is the fraction of fixed-point-free involutions (`Pairing`) satisfying the event.
--
--   Differences from the source:
--   - encoding: the two occurrences of c → constants c₁, c₂ > 0 chosen before m, h and t; reason: p.1: every occurrence of c denotes a possibly different real > 0
--   - encoding: probability over all matchings of [2]^m → fraction of Pairing([2]^m) (a ratio of Nat.card), with 1 ≤ m; reason: for m = 0 there is no matching of a single vertex and the probability is undefined; the hypothesis excludes only that case
--   - reading: C_π(h), "the correlation between h and f_π" → the signed correlation corr(h, f_π); reason: p.1 defines correlation signed, and the proof bounds W − E[W] from above; the |·| form follows by applying the signed one to h and h ⊕ 1 and enlarging c₁, shrinking c₂
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, (1), p.6

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_RevisitXor_mm

namespace RevisitXor

open OAI.MatchingSmoothing

/-- **Claim (1): tail bound for the correlation with a random `f_π`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), §1, (1), p.6: "Second we claim that for any fixed function h : [2]^n → [2] one has
P_π[C_π(h) ≥ t/M] ≤ 2 · 2^{−ct} (1) for t ≥ c log M, where C_π(h) is the correlation between h and
f_π, and the probability is over all matchings as above."

**Formalization Note.** `n = 2m` and `h` is read on the split `(x, y) ∈ [2]^m × [2]^m`. The two
occurrences of `c` are two absolute constants `c₁, c₂ > 0` (p.1 convention), chosen before `m`,
`h`, `t`. The probability is over the uniform law on fixed-point-free involutions (`Pairing`),
written as a ratio of cardinalities. `1 ≤ m` because for `m = 0` there is no such involution and the
probability is undefined. `C_π(h)` is the signed correlation. -/
theorem claim_1 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m → ∀ h : Cube m × Cube m → ZMod 2,
      ∀ t : ℝ, c₁ * Real.log ((2 : ℝ) ^ m) ≤ t →
        (Nat.card {π : Pairing (Cube m) // t / (2 : ℝ) ^ m ≤ corr h (mm π)} : ℝ) /
            Nat.card (Pairing (Cube m)) ≤ 2 * (2 : ℝ) ^ (-(c₂ * t)) := by sorry

end RevisitXor
