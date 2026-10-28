-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65k_rounded_total
-- name    : TaoFivePrimes.sine_bin_65k_rounded_total
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:56:29.875555+00:00
-- url     : https://prove2.me/theorems/84c4f5f0-ee89-4dc4-83e0-74f60a365e4b
-- title:
--   Sum of the rounded 65,000-height bin-weight bounds
-- statement:
--   Let $t_n$ be the stored integer weight bound for bin $n$. Then
--
--   $$
--   \frac{\sum_{n=0}^{179} t_n}{10^{21}}+\frac{81609874820}{10^{21}}\le\frac{115}{10^{11}}.
--   $$
--
--   This is an exact arithmetic identity and inequality for the recorded data; the validity of the data as bounds on zeta zeros is a separate question.
-- source:
--   Exact rational certificates for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic

theorem TaoFivePrimes.sine_bin_65k_rounded_total :
    (∑ i ∈ Finset.range 180, (TaoFivePrimes.sineBinTerm65k i:ℝ)/10^21) +
      (81609874820:ℝ)/10^21 ≤ (115/10^11:ℝ) := by sorry
