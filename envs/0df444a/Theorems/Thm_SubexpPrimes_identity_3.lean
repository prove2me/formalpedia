-- Prove2me | Theorems.Thm_SubexpPrimes_identity_3
-- name    : SubexpPrimes.identity_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:43.282589+00:00
-- url     : https://prove2.me/theorems/8fd32bdc-8772-49b6-9ede-6c590042fb82
-- title:
--   Identity (3) — the prime mass as a sum that never tests primality
-- statement:
--   For every constraint $C$ on $n$-bit strings, with no error,
--
--   $$
--   W_C=\sum_{e=1}^n\mu(e)\sum_{a\ge2,\ a^e<2^n}C(a^e)\sum_{db=a}\ln b\sum_{1\le c\le d,\ (c,d)=1}\cos\frac{2\pi c}{d}.
--   $$
--
--   The right-hand side involves integers related by multiplication and two non-integer quantities, the cosine and the logarithm, and each of those can be represented inside a network.
--
--   Differences from the source:
--   - encoding: C(a^e), for a constraint on integers → C on the n-bit string of a^e, most significant bit first; reason: a^e < 2ⁿ, so the string determines the integer
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), equation (3), §4, p.21

import Mathlib
import Definitions.Def_SubexpPrimes_primeMass

set_option autoImplicit false

namespace SubexpPrimes

open scoped ArithmeticFunction.Moebius Classical in
/-- **Identity (3)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), §4, p.21.

For every constraint `C` and every `n`, with no error,
`W_C = ∑_{e=1}^n µ(e) ∑_{a≥2, a^e<2ⁿ} C(a^e) ∑_{db=a} ln b ∑_{1≤c≤d, (c,d)=1} cos(2πc/d)`.

**Formalization Note.** `C(a^e)` is `C` on the `n`-bit string of `a^e`, most significant bit first.
Every `a` in the range satisfies `a ≤ a^e < 2ⁿ`, so `a` runs over `[2, 2ⁿ)` filtered by `a^e < 2ⁿ`. -/
theorem identity_3 (n : ℕ) (C : List Bool → Prop) :
    primeMass n C =
      ∑ e ∈ Finset.Icc 1 n, ((μ e : ℤ) : ℝ) *
        ∑ a ∈ (Finset.Ico 2 (2 ^ n)).filter (fun a => a ^ e < 2 ^ n),
          (if C (bitsOf n (a ^ e)) then 1 else 0) *
            ∑ p ∈ a.divisorsAntidiagonal, Real.log p.2 *
              ∑ c ∈ (Finset.Icc 1 p.1).filter (fun c => Nat.Coprime c p.1),
                Real.cos (2 * Real.pi * c / p.1) := by sorry

end SubexpPrimes
