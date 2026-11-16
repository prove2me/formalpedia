-- Prove2me | Theorems.Thm_SubexpPrimes_Supplement_theorem_7_1_complete_factorization
-- name    : SubexpPrimes.Supplement.theorem_7_1_complete_factorization
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:47:00.850207+00:00
-- url     : https://prove2.me/theorems/c2b898d2-6bd1-46df-b639-7865ff4cf705
-- title:
--   Theorem 7.1 — complete factorization in deterministic time $2^{O(n/\sqrt{\log n})}$ and polynomial space
-- statement:
--   There is a single deterministic machine and a constant $K$ such that for every $n$ and every integer $X$ with $2\le X<2^n$, given the $n$-bit binary string of $X$, the machine outputs the complete factorization of $X$, that is, the list of its prime factors with multiplicity in nondecreasing order, within
--
--   $$
--   2^{Kn/\sqrt{\log_2 n}}
--   $$
--
--   steps, and at every step of the run it has visited at most $K n^K$ tape cells.
--
--   So every $n$-bit integer $X\ge2$ can be factored completely in deterministic time $2^{O(n/\sqrt{\log n})}$ and polynomial space. The best previous deterministic bound was $2^{n/5+o(n)}$.
--
--   **Formalization Note** Since $2\le X<2^n$ forces $n\ge2$, $\log_2 n\ge1$. Each prime factor is output in binary, least significant bit first, and the list is framed by the standard list encoding.
--
--   Differences from the source:
--   - reading: n-bit integer X ≥ 2 → 2 ≤ X < 2ⁿ, input the n-bit string of X with leading zeros allowed; reason: the paper's notation, p.13; the stronger reading, since the bound is in the input length n
--   - encoding: factored completely → output Nat.primeFactorsList X (prime factors with multiplicity, nondecreasing), each in binary; reason: a list of the prime factors with multiplicity is the complete factorization; the order is the one the proof produces
--   - encoding: polynomial space → at most K nᴷ visited cells at every step, input tape included; reason: the published RunsWithin; the same form as the published goal
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 7.1, p.29 (PDF p.31); proof pp.29–30

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 7.1 (Complete factorization)** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), p.29.

Every `n`-bit integer `X ≥ 2` can be factored completely in deterministic time `2^{O(n/√log n)}` and
polynomial space: one machine, given the `n`-bit string of `X`, outputs the prime factors of `X` with
multiplicity, in time `2^{K n/√(log₂ n)}` and with at most `K nᴷ` visited cells at every step.

**Formalization Note.** The input is the `n`-bit string of `X`, most significant bit first, leading
zeros allowed (the paper's convention for `n`-bit integers, p.13); `2 ≤ X < 2ⁿ` forces `n ≥ 2`, so
`log₂ n ≥ 1`. The output is the list `Nat.primeFactorsList X` (nondecreasing, with multiplicity), each
factor as `countWord` (binary, least significant bit first), framed by `Encoding.encodeList`. One
machine and one constant `K` serve every `n` and `X`. -/
theorem theorem_7_1_complete_factorization :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ n X : ℕ, 2 ≤ X → X < 2 ^ n →
        RunsWithin M out (bitsOf n X) (Encoding.encodeList countWord X.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ))))
          ((K : ℝ) * (n : ℝ) ^ K) := by sorry

end SubexpPrimes.Supplement
