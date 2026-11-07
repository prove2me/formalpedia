-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_5_2_harmonic_count
-- name    : SubexpPrimes.lemma_5_2_harmonic_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:35.619209+00:00
-- url     : https://prove2.me/theorems/af5c82a6-336b-40ec-a080-5db775a4174e
-- title:
--   Lemma 5.2 — the harmonic count: $\ln b$ as a lattice-point count
-- statement:
--   Let $n,Q\ge1$, $B=2^{Q+2}$, $P=n+2Q+4$, and for $1\le b<2^n$ let $N(b)$ be the number of pairs $(u,y)\in\mathbb Z^2$ with $B<u\le Bb$, $y\ge0$ and $u(y+1)\le2^P$. Then
--
--   $$
--   0\le\ln b-2^{-P}N(b)\le2^{-Q-1}.
--   $$
--
--   Moreover, the relation on $(b,u,y)$ that defines these pairs has an explicit functional representation with $O(n+Q)$ edges and degree $O((n+Q)^{3/4})$, with $b$ on $n$ bits, $u$ on $n+Q+2$ bits and $y$ on $P$ bits.
--
--   A network with Boolean entries produces counts, so this writes the logarithm as a count times the fixed scale $2^{-P}$, which is applied outside the network.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: relations on integers and polynomials → predicates on one list of input bits, read off by slices, most significant bit first; reason: the convention of p.13; a word of fixed width stands for one integer
--   - encoding: pairs in ℤ² → pairs of natural numbers with y < 2^P; reason: every counted pair has u > 0, y ≥ 0 and y + 1 ≤ 2^P
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 5.2, p.25

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_ExplicitFamily
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_harmonicCount

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma 5.2 (Harmonic count)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.25.

Let `n, Q ≥ 1`, `B = 2^{Q+2}`, `P = n + 2Q + 4`. For `1 ≤ b < 2ⁿ`,
`0 ≤ ln b - 2^{-P} N(b) ≤ 2^{-Q-1}`. Moreover, the relation on `(b, u, y)` that defines the counted
pairs has an explicit functional representation with `O(n + Q)` edges and degree
`O((n + Q)^{3/4})`, with `b` on `n` bits, `u` on `n + Q + 2` bits, `y` on `P` bits.

**Formalization Note.** Each counted pair has exactly one encoding on those widths (p.25). The
relation on words of those widths is `B < u ≤ Bb` and `u(y + 1) ≤ 2^P`. -/
theorem lemma_5_2_harmonic_count :
    (∀ n Q b : ℕ, 1 ≤ n → 1 ≤ Q → 1 ≤ b → b < 2 ^ n →
      0 ≤ Real.log b - (2 : ℝ) ^ (-((n + 2 * Q + 4 : ℕ) : ℤ)) * harmonicCount n Q b ∧
      Real.log b - (2 : ℝ) ^ (-((n + 2 * Q + 4 : ℕ) : ℤ)) * harmonicCount n Q b ≤
        (2 : ℝ) ^ (-((Q : ℤ) + 1))) ∧
    HasLinearRep
      (fun a : ℕ × ℕ => Encoding.encodeList id [List.replicate a.1 true, List.replicate a.2 true])
      (fun a => 1 ≤ a.1 ∧ 1 ≤ a.2) (fun a => a.1 + a.2)
      (fun a => a.1 + (a.1 + a.2 + 2) + (a.1 + 2 * a.2 + 4))
      (fun a x =>
        let n := a.1
        let Q := a.2
        let b := bitsToNat (slice x 0 n)
        let u := bitsToNat (slice x n (n + Q + 2))
        let y := bitsToNat (slice x (n + (n + Q + 2)) (n + 2 * Q + 4))
        2 ^ (Q + 2) < u ∧ u ≤ 2 ^ (Q + 2) * b ∧ u * (y + 1) ≤ 2 ^ (n + 2 * Q + 4)) := by sorry

end SubexpPrimes
