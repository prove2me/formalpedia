-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg132
-- name    : WeakGoldbach.prime_in_4e18_window_proth_seg132
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T06:05:43.531461+00:00
-- url     : https://prove2.me/theorems/3139acb7-b7a9-4fe7-9a7d-b68b4f0d6689
-- title:
--   Prime in every window $(x,x+4\cdot10^{18})$: Proth ladder segment 132 of 782
-- statement:
--   For every natural number $x$ with
--
--   $$
--   16751921547149252491214849\le x< 16879798779794239694831617,
--   $$
--
--   there exists a prime $p$ with $x<p<x+4\cdot 10^{18}$.
--
--   Role: this is segment $132$ of $782$ consecutive segments covering $4\cdot10^{18}\le x\le 10^{26}$, the finite verification behind the parent node `WeakGoldbach.prime_in_4e18_window_4e18_to_1e26` (a prime in every window $(x,x+4\cdot10^{18})$ for $4\cdot10^{18}\le x\le10^{26}$). The segments meet end to end: segment $k$'s upper endpoint is segment $k+1$'s lower endpoint, the first lower endpoint is at most $4\cdot10^{18}$ and the last upper endpoint exceeds $10^{26}$. Both endpoints are primes of the form $k\cdot 2^{44}+1$ from a ladder of such primes with consecutive differences below $4\cdot10^{18}$.
--
--   **Formalization Note** The segment endpoints are the exact ladder primes produced by the certificate; the statement is unconditional and finite (it concerns only primes below $16879802779794239694831617$).
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, https://arxiv.org/abs/1305.3062, Section 4 (the prime ladder with consecutive gaps below 4e18, the source cited by the parent node); primality by Proth's theorem (F. Proth, Comptes rendus 87 (1878), p. 926). Finite verification of the range 4e18 <= x <= 1e26, ladder certificate segment 132 of 782

import Mathlib.Data.Nat.Prime.Defs

namespace WeakGoldbach

theorem prime_in_4e18_window_proth_seg132 (x : ℕ)
    (hxl : 16751921547149252491214849 ≤ x) (hx : x < 16879798779794239694831617) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by sorry

end WeakGoldbach
