-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_analytic_gamma_correlation
-- name    : TaoFivePrimes.rh_direct_132_analytic_gamma_correlation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:40:43.190609+00:00
-- url     : https://prove2.me/theorems/ff0f38d1-7d05-4bb5-ae8e-6b232a9f6e43
-- title:
--   Analytic and integer phase correlations for height 132
-- statement:
--   For a panel $0\le i<16$ and $0\le m<184$, let $b_{i,r}$ be the stored rational theta jet, $w_j$ its integration weight, and $e_l=(99\mathrm{i}/8)^l/l!$ the phase Taylor coefficients. Let $\Gamma_{i,m}$ be the published Gaussian-integer phase correlation, and let $W$ be the integer integration-weight denominator. Then
--
--   $$
--   \sum_{l=0}^{183-m}e_l\sum_{r=0}^{183-m-l}b_{i,r}w_{m+l+r}
--   =\frac{\Gamma_{i,m}}{10^{310}W\,8^{183}\,183!}.
--   $$
--
--   This exact finite identity connects the analytic quadrature coefficients to the integer data; it does not by itself assert any numerical approximation.
-- source:
--   The theta-jet and finite Mellin quadrature framework is due to sometik179, with theta/Mellin foundations by Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132Rule
import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Mathlib
open Complex Finset

theorem TaoFivePrimes.rh_direct_132_analytic_gamma_correlation (i m : ℕ) (hi : i<16) (hm : m<184) :
    (∑ l ∈ range (184-m), RHDirect132Rule.phaseJet l *
      ∑ r ∈ range (184-m-l), RHDirect132Rule.baseJet i r * RHDirect132Rule.weight (m+l+r)) =
      (((RHDirect132Integer.gammaRe i m:ℤ):ℂ) +
        Complex.I*((RHDirect132Integer.gammaIm i m:ℤ):ℂ))/
      ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
        ((8:ℂ)^183*((183:ℕ).factorial:ℂ))) := by sorry
