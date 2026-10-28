-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_block_107_1e3
-- name    : TaoFivePrimes.rh_verified_block_107_1e3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:52:20.768469+00:00
-- url     : https://prove2.me/theorems/26f4dce2-fe90-4da3-a65d-c70895a4b516
-- title:
--   RH on the remaining slab from height 107 to 1000
-- statement:
--   For every zero $s=\sigma+it$ of the Riemann zeta function in the open critical strip $0<\sigma<1$ and in the height range
--
--   $$
--   107\le t\le10^3,
--   $$
--
--   one has $\sigma=1/2$.
--
--   This is the remaining portion of the height-$100$ to $1000$ zero-location block after the preceding low-height certificates. The endpoints are included and zeros need not be simple.
-- source:
--   Restriction of the finite-height verification in D. J. Platt, Isolating some non-trivial zeros of zeta, Math. Comp. 86 (2017), 2449–2467, and Theorem 1.5 of T. Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/html/1201.6656v4. The lower endpoint is selected to meet the new zero-free rectangle 106–107.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.rh_verified_block_107_1e3 (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : 107 ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by sorry
