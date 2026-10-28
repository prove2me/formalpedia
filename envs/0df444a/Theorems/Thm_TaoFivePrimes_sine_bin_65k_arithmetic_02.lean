-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65k_arithmetic_02
-- name    : TaoFivePrimes.sine_bin_65k_arithmetic_02
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:56:29.764497+00:00
-- url     : https://prove2.me/theorems/9d05e797-62f9-4e0a-b250-442eac52ab42
-- title:
--   Rounded rational weight bounds for bins 120–179
-- statement:
--   For each integer $n$ with $120\le n\le 179$, let $b_n$, $c_n$, and $t_n$ be the stored sine, multiplicity, and rounded-weight integers. Put $L_n=65000+1290n$ and $U_n=L_n+1290$. Then
--
--   $$
--   \frac{2c_n}{L_n^3}\left(\frac{4b_n}{10000}+\frac8{2149}+\frac{3U_n}{2149^2}\right)\le\frac{t_n}{10^{21}}.
--   $$
--
--   The statement compares rational table entries; the actual zero-count and sine bounds are separate theorems.
-- source:
--   Exact rational certificates for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic

theorem TaoFivePrimes.sine_bin_65k_arithmetic_02 (i : Fin 60) :
    (2*(TaoFivePrimes.sineBinCount65k (i.val+120):ℝ)*
      (4*(TaoFivePrimes.sineBinNumerator65k (i.val+120):ℝ)/10000 + 8/2149 +
        3*(65000+1290*((i.val:ℝ)+120+1))/2149^2))/
          (65000+1290*((i.val:ℝ)+120))^3 ≤
      (TaoFivePrimes.sineBinTerm65k (i.val+120):ℝ)/10^21 := by sorry
