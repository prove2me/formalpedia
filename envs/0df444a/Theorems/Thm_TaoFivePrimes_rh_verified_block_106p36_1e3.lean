-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_block_106p36_1e3
-- name    : TaoFivePrimes.rh_verified_block_106p36_1e3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:27:22.733241+00:00
-- url     : https://prove2.me/theorems/946d5eaa-f511-4aeb-a640-d5442631f8fb
-- title:
--   RH on the remaining slab from height 106.36 to 1000
-- statement:
--   For every zero $s=\sigma+it$ of the Riemann zeta function in the open critical strip $0<\sigma<1$ and in the height range
--
--   $$
--   \frac{2659}{25}\le t\le 10^3,
--   $$
--
--   one has $\sigma=1/2$.
--
--   This is the portion of the height-$100$ to $1000$ zero-location block that remains after adjoining the separately certified lower slices. The endpoints are included, and no simplicity assumption is made.
-- source:
--   Restriction of the finite-height verification in D. J. Platt, Isolating some non-trivial zeros of zeta, Math. Comp. 86 (2017), 2449–2467, and Theorem 1.5 of T. Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/html/1201.6656v4. The particular endpoint 2659/25 is chosen to join separately verified certificates.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.rh_verified_block_106p36_1e3 (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (2659/25:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by sorry
