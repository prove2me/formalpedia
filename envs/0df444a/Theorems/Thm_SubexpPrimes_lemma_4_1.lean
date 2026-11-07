-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_4_1
-- name    : SubexpPrimes.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:32.862502+00:00
-- url     : https://prove2.me/theorems/1210a842-f81f-4730-bde5-736168957361
-- title:
--   Lemma 4.1 — Ramanujan's formula with unique witnesses, and the formulas for $\Lambda$ and for primes
-- statement:
--   1. (Ramanujan) For $d\ge1$,
--
--   $$
--   \mu(d)=\sum_{1\le c\le d,\ (c,d)=1}\cos(2\pi c/d).
--   $$
--
--   Moreover, the triples of integers $(c,c',k)$ with $cc'=kd+1$, $1\le c,c'\le d$ and $k\ge0$ correspond bijectively, by $(c,c',k)\mapsto c$, to the units $c$ modulo $d$, and every such triple has $k<d$.
--
--   2. For $a\ge1$, $\Lambda(a)=\sum_{db=a}\mu(d)\ln b$, where $d$ and $b$ range over positive integers.
--
--   3. For $2\le m<2^n$,
--
--   $$
--   (\ln m)\,\mathbf 1[m\text{ prime}]=\sum_{e=1}^n\mu(e)\sum_{a\ge2,\ a^e=m}\Lambda(a).
--   $$
--
--   The networks of the paper use these exact ranges of summation, and the witnesses let a network sum over the units without counting any unit twice.
--
--   Differences from the source:
--   - encoding: triples of integers with k ≥ 0 → triples of natural numbers; reason: the printed ranges make all three nonnegative
--   - encoding: the sum over a ≥ 2 with a^e = m → a in [2, m], filtered by a^e = m; reason: every such a satisfies a ≤ m
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 4.1, p.20

import Mathlib

set_option autoImplicit false

namespace SubexpPrimes

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt in
/-- **Lemma 4.1** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.20.

(a) (Ramanujan) For `d ≥ 1`, `µ(d) = ∑_{1≤c≤d, (c,d)=1} cos(2πc/d)`; moreover the triples
`(c, c′, k)` with `cc′ = kd + 1`, `1 ≤ c, c′ ≤ d`, `k ≥ 0` correspond bijectively, by
`(c, c′, k) ↦ c`, to the units `c` modulo `d` in `[1, d]`, and every such triple has `k < d`.
(b) For `a ≥ 1`, `Λ(a) = ∑_{db=a} µ(d) ln b`.
(c) For `2 ≤ m < 2ⁿ`, `(ln m) 1[m prime] = ∑_{e=1}^n µ(e) ∑_{a≥2, a^e=m} Λ(a)`.

**Formalization Note.** The triples are over `ℕ`, because the printed ranges make all three
nonnegative. In (c) the inner `a` ranges over `2 ≤ a ≤ m`, which contains every `a` with `a^e = m`. -/
theorem lemma_4_1 :
    (∀ d : ℕ, 1 ≤ d →
      ((μ d : ℤ) : ℝ) = ∑ c ∈ (Finset.Icc 1 d).filter (fun c => Nat.Coprime c d),
        Real.cos (2 * Real.pi * c / d)) ∧
    (∀ d : ℕ, 1 ≤ d →
      Set.BijOn (fun t : ℕ × ℕ × ℕ => t.1)
        {t | t.1 * t.2.1 = t.2.2 * d + 1 ∧ 1 ≤ t.1 ∧ t.1 ≤ d ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ d}
        {c | 1 ≤ c ∧ c ≤ d ∧ Nat.Coprime c d}) ∧
    (∀ d c c' k : ℕ, 1 ≤ d → c * c' = k * d + 1 → 1 ≤ c → c ≤ d → 1 ≤ c' → c' ≤ d → k < d) ∧
    (∀ a : ℕ, 1 ≤ a →
      Λ a = ∑ p ∈ a.divisorsAntidiagonal, ((μ p.1 : ℤ) : ℝ) * Real.log p.2) ∧
    (∀ n m : ℕ, 2 ≤ m → m < 2 ^ n →
      Real.log m * (if m.Prime then 1 else 0) =
        ∑ e ∈ Finset.Icc 1 n, ((μ e : ℤ) : ℝ) *
          ∑ a ∈ (Finset.Icc 2 m).filter (fun a => a ^ e = m), Λ a) := by sorry

end SubexpPrimes
