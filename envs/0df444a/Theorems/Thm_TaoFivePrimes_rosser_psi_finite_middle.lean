-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_psi_finite_middle
-- name    : TaoFivePrimes.rosser_psi_finite_middle
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T12:51:43.229964+00:00
-- url     : https://prove2.me/theorems/d7089f63-d516-4c70-a5f5-f1ae1e917931
-- title:
--   Finite Rosser bound between 1000 and 10^8
-- statement:
--   For every integer strictly between 1000 and 10^8, the second Chebyshev function satisfies $$\psi(n)<1.03883n.$$ This is the remaining finite certificate obligation in a range decomposition of the uniform Rosser--Schoenfeld bound. The small range through 1000 is proved separately by exact LCM certificates; the range at least 10^8 follows from an explicit two-sided Chebyshev estimate. This finite obligation is open: numerical interval scouting is not a formal proof.
-- source:
--   Finite restriction of Prove2Me theorem TaoFivePrimes.rosser_schoenfeld_psi_bound (cf6be7a8-2493-479a-9d57-6ee8535546d1), whose source is Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers (1962), Theorem 12. The endpoints 1000 and 10^8 are specific to this formal range decomposition, not claimed to be a separately numbered theorem in that paper.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.rosser_psi_finite_middle (n : ℕ) (hn : 1000 < n) (hN : n < 10 ^ 8) : Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by sorry
