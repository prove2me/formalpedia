-- Prove2me | Theorems.Thm_PiIrrationality_mahler_numerical_estimates
-- name    : PiIrrationality.mahler_numerical_estimates
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T23:52:58.241737+00:00
-- url     : https://prove2.me/theorems/104f7872-60e7-452d-9617-ef6be8e68236
-- title:
--   Mahler (1953), §4 numerical estimates: the (n+1)^22, n^{11/2}, q^{10}-transfer and coefficient bounds for n ≥ 50
-- statement:
--   This is the elementary numerical chain of Mahler's 1953 paper on rational approximations to π, stated in §4 (original p. 32). Let n be a natural number with n ≥ 50 and q any natural number. Then:
--
--   (i) (n+1)^22 < 10^{0.7514n} and n^{11/2} < 10^{0.1869n};
--   (ii) if 10^{3.4181n} > 10^{0.4936n} · q^{10} then 10^{2.9245n} > q^{10};
--   (iii) 10 · 10! · 2^{30} · (n+1)^{22} · 2^{2.6n} < 10^{8.9101n}.
--
--   All powers with real exponents are real powers (rpow); powers with natural exponents (22, 10, 30) are natural-number powers; 10! is Nat.factorial. These are the four threshold estimates feeding Mahler's formulas (12)–(13): (i) controls the auxiliary-polynomial coefficient growth, (ii) transfers the hypothesis 10^{3.4181n} > 10^{0.4936n} q^{10} into the cleaner exponent 2.9245n > 10 log_{10} q, and (iii) is the final coefficient-size check that makes the remainder estimate dominate. The statement is unconditional and provable by rpow/log monotonicity plus the n ≥ 50 thresholds alone — no transcendence input is needed.
-- source:
--   K. Mahler, On the approximation of π, Nederl. Akad. Wetensch. Proc. Ser. A 56 = Indag. Math. 15 (1953), 30–42, §4, numerical estimates on original p. 32 (Documenta Math. Extra Volume Mahler Selecta (2019), p. 560). Reprint: https://content.ems.press/assets/public/full-texts/books/252/chapters/online-pdf/252-chapter-4986.pdf . Decomposition child C of PiIrrationality.mahler_1953_eq13; see ~/workspace/p2m_harness/mahler_pi_triage.md §3.

import Mathlib

theorem PiIrrationality.mahler_numerical_estimates (n q : ℕ) (hn : 50 ≤ n) :
    ((n : ℝ) + 1) ^ (22 : ℕ) < (10 : ℝ) ^ ((0.7514 : ℝ) * n)
    ∧ (n : ℝ) ^ ((11 / 2 : ℝ)) < (10 : ℝ) ^ ((0.1869 : ℝ) * n)
    ∧ ((10 : ℝ) ^ ((3.4181 : ℝ) * n) > (10 : ℝ) ^ ((0.4936 : ℝ) * n) * (q : ℝ) ^ (10 : ℕ) →
        (10 : ℝ) ^ ((2.9245 : ℝ) * n) > (q : ℝ) ^ (10 : ℕ))
    ∧ (10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (30 : ℕ)
        * (((n : ℝ) + 1) ^ (22 : ℕ)) * (2 : ℝ) ^ ((2.6 : ℝ) * n)
        < (10 : ℝ) ^ ((8.9101 : ℝ) * n) := by
  sorry
