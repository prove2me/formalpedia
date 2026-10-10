-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg505
-- name    : WeakGoldbach.prime_in_4e18_window_proth_seg505
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T16:58:16.471443+00:00
-- url     : https://prove2.me/theorems/41f1c49c-fc0a-4e38-ad6e-1d289b0fbbd4
-- title:
--   Prime in every window $(x,x+4\cdot10^{18})$: Proth ladder segment 505 of 782
-- statement:
--   For every natural number $x$ with
--
--   $$
--   64450129525124825276743681\le x< 64578006758948488945336321,
--   $$
--
--   there exists a prime $p$ with $x<p<x+4\cdot 10^{18}$.
--
--   Role: this is segment $505$ of $782$ consecutive segments covering $4\cdot10^{18}\le x\le 10^{26}$, the finite verification behind the parent node `WeakGoldbach.prime_in_4e18_window_4e18_to_1e26` (a prime in every window $(x,x+4\cdot10^{18})$ for $4\cdot10^{18}\le x\le10^{26}$). The segments meet end to end: segment $k$'s upper endpoint is segment $k+1$'s lower endpoint, the first lower endpoint is at most $4\cdot10^{18}$ and the last upper endpoint exceeds $10^{26}$. Both endpoints are primes of the form $k\cdot 2^{44}+1$ from a ladder of such primes with consecutive differences below $4\cdot10^{18}$.
--
--   **Formalization Note** The segment endpoints are the exact ladder primes produced by the certificate; the statement is unconditional and finite (it concerns only primes below $64578010758948488945336321$).
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, https://arxiv.org/abs/1305.3062, Section 4 (the prime ladder with consecutive gaps below 4e18, the source cited by the parent node); primality by Proth's theorem (F. Proth, Comptes rendus 87 (1878), p. 926). Finite verification of the range 4e18 <= x <= 1e26, ladder certificate segment 505 of 782

import Mathlib.Data.Nat.Prime.Defs

namespace WeakGoldbach

theorem prime_in_4e18_window_proth_seg505 (x : ℕ)
    (hxl : 64450129525124825276743681 ≤ x) (hx : x < 64578006758948488945336321) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by sorry

end WeakGoldbach
