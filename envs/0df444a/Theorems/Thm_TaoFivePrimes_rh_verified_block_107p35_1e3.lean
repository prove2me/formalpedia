-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_block_107p35_1e3
-- name    : TaoFivePrimes.rh_verified_block_107p35_1e3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:59:05.52091+00:00
-- url     : https://prove2.me/theorems/24d04556-5805-4c57-871d-e16b7471ae68
-- title:
--   RH on the remaining slab from height 107.35 to 1000
-- statement:
--   For every zero $s=\sigma+it$ of the Riemann zeta function in the open critical strip $0<\sigma<1$ and with
--
--   $$
--   107.35\le t\le10^3,
--   $$
--
--   one has $\sigma=1/2$. The endpoints are included and no simplicity assumption is made.
--
--   This is the portion of the height-$100$ to $1000$ zero-location verification remaining after adjoining the separately certified slice from $107$ to $107.35$.
-- source:
--   Restriction of the finite-height verification in D. J. Platt, Isolating some non-trivial zeros of zeta, Math. Comp. 86 (2017), 2449–2467, and Theorem 1.5 of T. Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/html/1201.6656v4. The lower endpoint is selected to meet the separately certified 107–107.35 slice.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.rh_verified_block_107p35_1e3 (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (2147/20:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by sorry
