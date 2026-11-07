-- Prove2me | Theorems.Thm_SubexpPrimes_theorem_1_least_prime
-- name    : SubexpPrimes.theorem_1_least_prime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:10.504835+00:00
-- url     : https://prove2.me/theorems/0d6988c5-18f3-4264-9107-23fac0a5e731
-- title:
--   Theorem 1 — a deterministic machine outputs the least $n$-bit prime in time $2^{O(n/\sqrt{\log n})}$ and polynomial space
-- statement:
--   Let $p_n$ denote the least prime in $[2^{n-1},2^n)$, which exists for every $n\ge2$ by Bertrand's postulate. There is a deterministic algorithm that, on input $1^n$, outputs $p_n$ for every $n\ge2$. It runs in time
--
--   $$
--   2^{O(n/\sqrt{\log n})}
--   $$
--
--   and uses space polynomial in $n$.
--
--   The previous best deterministic bound was $2^{n/2+o(n)}$, due to Lagarias and Odlyzko. The result holds at every input length, for a prime defined independently of the algorithm.
--
--   **Formalization Note** One machine for every $n$, with the constant fixed before $n$, and the logarithm base two. On $n\ge2$ the logarithm is at least $1$. The space clause holds at every step and counts the input tape.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: O(·) in the exponent and polynomial space → one constant C with exponent C n/√(log₂ n) and space C n^C, quantified before n; reason: this is what O(·) means for one algorithm; a constant absorbs small n, since n/√(log₂ n) is positive on n ≥ 2
--   - encoding: on input 1ⁿ, outputs pₙ → input List.replicate n true; output countWord p (binary, least significant bit first) on a designated tape of the halted machine; reason: the paper fixes no output format
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 1, p.4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 1 (Primes)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.4.

There is a deterministic algorithm that, on input `1ⁿ`, outputs `pₙ`, the least prime in
`[2^{n-1}, 2ⁿ)`, for every `n ≥ 2`, in time `2^{O(n/√log n)}` and in space polynomial in `n`.

**Formalization Note.** One machine for every `n`, and the constant before `n`, so the theorem holds at
every input length, deterministically and with the exact least prime. Input `1ⁿ` is
`List.replicate n true`; the output is `countWord p`, the binary digits of `p`, least significant
first, on a designated tape of the halted machine. `log` is base two, as in the paper (p.13); at
`n ≥ 2`, `log₂ n ≥ 1`. The space clause holds at every step of the run and counts the input tape. -/
theorem theorem_1_least_prime :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
      ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ,
        IsLeast {q : ℕ | q.Prime ∧ 2 ^ (n - 1) ≤ q ∧ q < 2 ^ n} p ∧
        RunsWithin A out (List.replicate n true) (countWord p)
          ((2 : ℝ) ^ ((C : ℝ) * (n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ))))
          ((C : ℝ) * (n : ℝ) ^ C) := by sorry

end SubexpPrimes
