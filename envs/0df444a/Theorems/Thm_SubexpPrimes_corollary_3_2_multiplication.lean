-- Prove2me | Theorems.Thm_SubexpPrimes_corollary_3_2_multiplication
-- name    : SubexpPrimes.corollary_3_2_multiplication
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:53.99533+00:00
-- url     : https://prove2.me/theorems/b37fead3-0276-4197-a7d1-72eebf948de0
-- title:
--   Corollary 3.2 — multiplication with $O(n)$ edges and degree $O(n^{3/4})$
-- statement:
--   For every $n\ge1$, the following relations have explicit functional representations with $O(n)$ edges and degree $O(n^{3/4})$:
--
--   1. $uv=z$, for integers $0\le u,v<2^n$ and $0\le z<2^{2n}$;
--   2. $D=AB$, for polynomials $A,B\in\mathbb F_2[X]$ of degree less than $n$.
--
--   No circuit is known that does this: schoolbook multiplication has $\Theta(n^2)$ wires. All later relations are built on these two.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: relations on integers and polynomials → predicates on one list of input bits, read off by slices, most significant bit first; reason: the convention of p.13; a word of fixed width stands for one integer
--   - encoding: D = AB with no width printed for D → D on 2n coefficient bits; reason: the product has degree at most 2n − 2, so this width holds every product
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Corollary 3.2, p.18

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_ExplicitFamily
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Corollary 3.2 (Multiplication)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.18.

(a) `uv = z`, for `0 ≤ u, v < 2ⁿ` and `0 ≤ z < 2^{2n}`, and (b) `D = AB`, for polynomials
`A, B ∈ F₂[X]` of degree less than `n`, have functional representations with `O(n)` edges and degree
`O(n^{3/4})`, explicit: built from `1ⁿ` in polynomial time, with polynomial-time entries.

**Formalization Note.** Input words are `u ++ v ++ z`, of widths `n, n, 2n`, most significant bit
first; `A`, `B`, `D` are `n`, `n`, `2n` coefficient words, most significant coefficient first. -/
theorem corollary_3_2_multiplication :
    HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n)
      (fun n => 4 * n)
      (fun n x => bitsToNat (slice x 0 n) * bitsToNat (slice x n n) =
        bitsToNat (slice x (2 * n) (2 * n))) ∧
    HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n)
      (fun n => 4 * n)
      (fun n x => polyOf (slice x (2 * n) (2 * n)) =
        polyOf (slice x 0 n) * polyOf (slice x n n)) := by sorry

end SubexpPrimes
