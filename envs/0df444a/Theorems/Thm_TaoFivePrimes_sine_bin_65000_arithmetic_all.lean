-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65000_arithmetic_all
-- name    : TaoFivePrimes.sine_bin_65000_arithmetic_all
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:04:22.02038+00:00
-- url     : https://prove2.me/theorems/ba784263-40d1-4faf-91ce-65efad97a67d
-- title:
--   Rational weight bounds for all 180 height bins
-- statement:
--   For $0\le n<180$, let $b_n$, $c_n$, and $t_n$ be the stored integer sine, multiplicity, and weight data, and put $L_n=65000+1290n$ and $U_n=L_n+1290$. Then
--
--   $$
--   \frac{2c_n}{L_n^3}\left(\frac{4b_n}{10000}+\frac8{2149}+\frac{3U_n}{2149^2}\right)\le\frac{t_n}{10^{21}}.
--   $$
--
--   This unifies the three separately verified groups of sixty rational comparisons.
-- source:
--   Combines the independently checked grouped certificates for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

theorem TaoFivePrimes.sine_bin_65000_arithmetic_all (i : Fin 180) :
    (2*(TaoFivePrimes.sineBinCount65k i.val:ℝ)*
      (4*(TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000 + 8/2149 +
        3*(65000+1290*((i.val:ℝ)+1))/2149^2))/
          (65000+1290*(i.val:ℝ))^3 ≤
      (TaoFivePrimes.sineBinTerm65k i.val:ℝ)/10^21 := by sorry
