-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_envelope_log_four_comparison
-- name    : TaoFivePrimes.dusart_envelope_log_four_comparison
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-02T15:55:54.418979+00:00
-- url     : https://prove2.me/theorems/a264a5c1-7f18-4243-a7db-34304a191659
-- title:
--   Exponential-to-fourth-logarithmic comparison for Dusart’s tail estimate
-- statement:
--   Let $R=5.69693$. For every real $t\ge13900$,
--
--   $$\sqrt{\frac8\pi}\,\sqrt{\sqrt{t/R}}\,e^{-\sqrt{t/R}}\le\frac{151.3}{t^4}.$$
--
--   This elementary comparison converts the exponential envelope in Dusart's explicit Chebyshev estimate into the fourth-logarithmic error bound by taking $t=\log x$. It isolates the numerical part of the tail argument from the analytic prime-number-theorem input. The stated constants are exact rational numbers.
-- source:
--   Elementary comparison derived for the large-value argument of P. Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018), Theorem 4.2, printed p.237, https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf. The exponential envelope is Dusart HDR Théorème45 p.37, https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf. This numerical inequality is a derived auxiliary lemma, not a verbatim theorem of either source.

import Mathlib

theorem TaoFivePrimes.dusart_envelope_log_four_comparison (t : ℝ) (ht : 13900 ≤ t) :
    Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (t / (569693 / 100000 : ℝ))) *
      Real.exp (-Real.sqrt (t / (569693 / 100000 : ℝ))) ≤
      (1513 / 10 : ℝ) / t ^ 4 := by sorry
