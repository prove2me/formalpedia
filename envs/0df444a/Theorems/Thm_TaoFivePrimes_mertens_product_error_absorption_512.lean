-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_product_error_absorption_512
-- name    : TaoFivePrimes.mertens_product_error_absorption_512
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:44:40.294061+00:00
-- url     : https://prove2.me/theorems/006b99d0-be53-4cef-94d6-ec869ccaa0e2
-- title:
--   Elementary absorption of the Mertens product and tail errors above 512
-- statement:
--   For every real $x\ge512$,
--
--   $$\frac{2}{\sqrt{x}\log x}+\frac1{\lfloor x\rfloor}\le\frac4{\log^3x}.$$
--
--   This elementary real-variable inequality absorbs the relative error in the Rosser–Schoenfeld finite-range Mertens product bound and the elementary $1/\lfloor x\rfloor$ correction-tail bound. It contains no prime-counting estimate.
-- source:
--   Elementary auxiliary inequality for TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small; derived by comparing the explicit error terms in Rosser–Schoenfeld (1962), Theorem 23 (4.10), and TaoFivePrimes.mertens_tail_upper.

import Mathlib

theorem TaoFivePrimes.mertens_product_error_absorption_512 (x : ℝ) (hx : 512 ≤ x) :
    2 / (Real.sqrt x * Real.log x) + 1 / (⌊x⌋₊ : ℝ) ≤ 4 / (Real.log x) ^ 3 := by sorry
