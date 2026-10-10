-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp09
-- name    : WeakGoldbach.prime_in_4e18_window_proth_grp09
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:15:12.200982+00:00
-- url     : https://prove2.me/theorems/d783c177-2030-4604-bb04-d2b0e05b3ed3
-- title:
--   Prime in every window $(x,x+4\cdot10^{18})$: Proth ladder block 9 of 16 (segments 393-441)
-- statement:
--   For every natural number $x$ with
--
--   $$
--   50127879408826535316029441\le x< 56393863834836779545919489,
--   $$
--
--   there exists a prime $p$ with $x<p<x+4\cdot 10^{18}$.
--
--   Role: this is block $9$ of $16$ consecutive blocks covering $4\cdot10^{18}\le x\le 10^{26}$, the finite verification behind the parent node `WeakGoldbach.prime_in_4e18_window_4e18_to_1e26` (a prime in every window $(x,x+4\cdot10^{18})$ for $4\cdot10^{18}\le x\le10^{26}$). The block spans exactly the range of the ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg393` through `WeakGoldbach.prime_in_4e18_window_proth_seg441` (segments $393$ to $441$ of $782$) and has the same form. The blocks meet end to end: block $k$'s upper endpoint is block $k+1$'s lower endpoint, the first lower endpoint is at most $4\cdot10^{18}$ and the last upper endpoint exceeds $10^{26}$. Both endpoints are primes of the form $k\cdot 2^{44}+1$ from a ladder of such primes with consecutive differences below $4\cdot10^{18}$.
--
--   **Formalization Note** The block endpoints are the exact ladder primes produced by the certificate; the statement is unconditional and finite (it concerns only primes below $56393867834836779545919489$).
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, https://arxiv.org/abs/1305.3062, Section 4 (the prime ladder with consecutive gaps below 4e18, the source cited by the parent node); primality by Proth's theorem (F. Proth, Comptes rendus 87 (1878), p. 926). Finite verification of the range 4e18 <= x <= 1e26, ladder block 9 of 16 = ladder certificate segments 393-441 of 782

import Mathlib.Data.Nat.Prime.Defs

namespace WeakGoldbach

theorem prime_in_4e18_window_proth_grp09 (x : ℕ)
    (hxl : 50127879408826535316029441 ≤ x) (hx : x < 56393863834836779545919489) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by sorry

end WeakGoldbach
