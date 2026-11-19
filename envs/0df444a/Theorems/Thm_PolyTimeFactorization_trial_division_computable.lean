-- Prove2me | Theorems.Thm_PolyTimeFactorization_trial_division_computable
-- name    : PolyTimeFactorization.trial_division_computable
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T16:12:30.1947+00:00
-- url     : https://prove2.me/theorems/d9cb8982-dc1b-4760-b986-c13ca64745cf
-- title:
--   Semiprime factorization is Turing-computable (trial-division baseline)
-- statement:
--   There is a total function $f:\mathbb{N}\to\mathbb{N}\times\mathbb{N}$, computable by a Turing machine with no time bound, that factors every semiprime: for all primes $p$ and $q$ (possibly equal), $f(pq)=(\min(p,q),\max(p,q))$.
--
--   This is the computability baseline of the mission — the goal with the polynomial-time requirement removed. Trial division supplies such an $f$, for instance $f(n)=(\mathrm{minFac}(n),\,n/\mathrm{minFac}(n))$, at exponential cost.
--
--   **Formalization Note.** Computability is Mathlib's `Turing.TM2Computable` with the binary input encoding `encodeNat` and the product output encoding `encodingProd encodingNatBool encodingNatBool`. Because `TM2Computable` is a bundled structure rather than a proposition, the existence of a machine is expressed with `Nonempty`.
-- source:
--   Folklore (trial division); see https://en.wikipedia.org/wiki/Trial_division and R. Crandall & C. Pomerance, Prime Numbers: A Computational Perspective, 2nd ed., Springer (2005), https://doi.org/10.1007/0-387-28979-8

import Mathlib
open Computability Turing

namespace PolyTimeFactorization

theorem trial_division_computable :
    ∃ f : ℕ → ℕ × ℕ,
      Nonempty (TM2Computable encodeNat (encodingProd encodingNatBool encodingNatBool).encode f) ∧
      ∀ p q : ℕ, p.Prime → q.Prime → f (p * q) = (min p q, max p q) := by sorry

end PolyTimeFactorization
