-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp02
-- name    : WeakGoldbach.prime_in_4e18_window_proth_grp02
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:12:26.788077+00:00
-- url     : https://prove2.me/theorems/9c72c682-1baf-435f-9cb3-90dd150bb02d
-- title:
--   Prime in every window $(x,x+4\cdot10^{18})$: Proth ladder block 2 of 16 (segments 50-98)
-- statement:
--   For every natural number $x$ with
--
--   $$
--   6265988425752071102267393\le x< 12531972851867868448423937,
--   $$
--
--   there exists a prime $p$ with $x<p<x+4\cdot 10^{18}$.
--
--   Role: this is block $2$ of $16$ consecutive blocks covering $4\cdot10^{18}\le x\le 10^{26}$, the finite verification behind the parent node `WeakGoldbach.prime_in_4e18_window_4e18_to_1e26` (a prime in every window $(x,x+4\cdot10^{18})$ for $4\cdot10^{18}\le x\le10^{26}$). The block spans exactly the range of the ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg050` through `WeakGoldbach.prime_in_4e18_window_proth_seg098` (segments $50$ to $98$ of $782$) and has the same form. The blocks meet end to end: block $k$'s upper endpoint is block $k+1$'s lower endpoint, the first lower endpoint is at most $4\cdot10^{18}$ and the last upper endpoint exceeds $10^{26}$. Both endpoints are primes of the form $k\cdot 2^{44}+1$ from a ladder of such primes with consecutive differences below $4\cdot10^{18}$.
--
--   **Formalization Note** The block endpoints are the exact ladder primes produced by the certificate; the statement is unconditional and finite (it concerns only primes below $12531976851867868448423937$).
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up to 8.875e30, arXiv:1305.3062v2, https://arxiv.org/abs/1305.3062, Section 4 (the prime ladder with consecutive gaps below 4e18, the source cited by the parent node); primality by Proth's theorem (F. Proth, Comptes rendus 87 (1878), p. 926). Finite verification of the range 4e18 <= x <= 1e26, ladder block 2 of 16 = ladder certificate segments 50-98 of 782

import Mathlib.Data.Nat.Prime.Defs

namespace WeakGoldbach

theorem prime_in_4e18_window_proth_grp02 (x : ℕ)
    (hxl : 6265988425752071102267393 ≤ x) (hx : x < 12531972851867868448423937) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by sorry

end WeakGoldbach
