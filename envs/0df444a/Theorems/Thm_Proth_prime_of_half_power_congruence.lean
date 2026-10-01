-- Prove2me | Theorems.Thm_Proth_prime_of_half_power_congruence
-- name    : Proth.prime_of_half_power_congruence
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-23T23:23:03.044994+00:00
-- url     : https://prove2.me/theorems/bf1948d8-005c-4cd2-9528-dbeb4d56084f
-- title:
--   Proth's primality criterion from a half-power congruence
-- statement:
--   Let $n,k,a$ be natural numbers with $n\ge1$ and $0<k<2^n$. Put $N=k2^n+1$. If
--
--   $$a^{(N-1)/2}\equiv-1\pmod N,$$
--
--   then $N$ is prime.
--
--   The criterion gives a primality certificate that can be checked by modular exponentiation. It applies to the Proth primes used in prime ladders, including Helfgott and Platt's finite verification method. This sufficient direction requires no additional hypothesis on the Jacobi symbol. It also does not require k to be odd, although that condition is usual in the classical definition of a Proth number; the displayed hypotheses suffice by Pocklington's criterion.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, Section 2, Theorem 2.3, p. 2, https://arxiv.org/pdf/1305.3062. The congruence alone is sufficient by Pocklington's criterion; the Jacobi-symbol condition in the source's procedure guides the choice of candidate. Formalization adapted from PrimeCert (Kenny Lau and Bhavik Mehta), revision ca5b4626afef3fe6a27834648f1b142edbe8d71e, and Gershon Bialer's Proth specialization in ternary-goldbach-lean, revision 27df23af6a712895f22204d0d81102baa74f0ebe. Notices and licenses are preserved in the proof.

import Mathlib

theorem Proth.prime_of_half_power_congruence (n k a : ℕ)
    (hn : 1 ≤ n) (hk : 0 < k) (hkF : k < 2 ^ n)
    (hcong : a ^ ((k * 2 ^ n) / 2) % (k * 2 ^ n + 1) = k * 2 ^ n) :
    Nat.Prime (k * 2 ^ n + 1) := by sorry
