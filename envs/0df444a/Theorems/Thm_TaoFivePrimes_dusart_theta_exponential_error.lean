-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_exponential_error
-- name    : TaoFivePrimes.dusart_theta_exponential_error
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-02T15:55:45.176189+00:00
-- url     : https://prove2.me/theorems/8b054cf2-daad-4b17-b1af-2c842d4b5f87
-- title:
--   Dusart's explicit exponential error bound for the Chebyshev theta function
-- statement:
--   Set $R=5.69693$ and $X=\sqrt{\log x/R}$. For every positive real $x$ satisfying $\log x\ge70R$, the Chebyshev function $\vartheta(x)=\sum_{p\le x}\log p$ satisfies
--
--   $$|\vartheta(x)-x|<x\sqrt{\frac8\pi}\,X^{1/2}e^{-X}.$$
--
--   This is the theta-function part of Dusart's explicit zero-free-region estimate, specialized to Kadiri's admissible constant $R=5.69693$. The hypothesis implies $X\ge\sqrt{70}>8.36$ and $X>8/R$, meeting both thresholds of the source theorem. It provides a reusable analytic input for converting exponential decay into explicit inverse powers of $\log x$, including the large-value argument in Dusart's 2018 Theorem 4.2.
--
--   This statement remains an analytic proof obligation; it is not a certificate that the zero-free-region argument has been formalized.
-- source:
--   P. Dusart, Estimates of ψ, θ for large values of x without the Riemann hypothesis, Math. Comp. 85 (2016), 875–888, Theorem 1.1, DOI 10.1090/S0025-5718-2015-03005-1. Primary author restatement: HDR, Théorème 45, printed p.37, and proof of Corollaire 46, printed p.46 (explicitly permits R=5.69693), https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf. Specialization uses log x ≥ 70R to imply X ≥ max(8.36,8/R).

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.dusart_theta_exponential_error
    (x : ℝ) (hx : 0 < x)
    (hlog : 70 * (569693 / 100000 : ℝ) ≤ Real.log x) :
    |Chebyshev.theta x - x| <
      x * Real.sqrt (8 / Real.pi) *
        Real.sqrt (Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) *
        Real.exp (-Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) := by sorry
