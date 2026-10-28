-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_131p15_133p2
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_131p15_133p2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:35:47.112708+00:00
-- url     : https://prove2.me/theorems/69ef5adb-6f3f-4338-830f-9acf40d16730
-- title:
--   Zeta is zero-free at heights 131.15–133.2
-- statement:
--   For $s=\sigma+it$ with $0<\sigma<1$ and $131.15\le t\le133.2$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both height endpoints are included. This rectangle is part of a finite-height zero-location argument.
-- source:
--   Local xi/Taylor and Bernstein methods of sometik179, with theta/Mellin foundations due to Gabewhigham; the height-132 disk estimate has a separate exact-rounding dependency.

import Mathlib

theorem TaoFivePrimes.zeta_zero_free_rectangle_131p15_133p2 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (2623/20:ℝ) ≤ s.im) (hb : s.im ≤ (666/5:ℝ)) : riemannZeta s ≠ 0 := by sorry
