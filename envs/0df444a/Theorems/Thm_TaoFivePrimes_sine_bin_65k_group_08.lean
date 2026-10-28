-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_08
-- name    : TaoFivePrimes.sine_bin_65k_group_08
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:24.878499+00:00
-- url     : https://prove2.me/theorems/52de13a5-463a-466e-95b9-475e8b327637
-- title:
--   Sine-square enclosures for 65,000-height bins 96–107
-- statement:
--   For each integer $n$ with $96\le n\le 107$, let $b_n$ be the stored rational-enclosure numerator. If
--
--   $$
--   \frac{65000+1290n}{4302}\le x\le\frac{65000+1290(n+1)}{4298},
--   $$
--
--   then $\sin^2 x\le b_n/10000$. The displayed intervals cover the phase of the smoothed kernel for the corresponding zero-height bin when the smoothing denominator is $2150$.
-- source:
--   Exact interval certificate generated from the proved sine-square interval enclosure; intended for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem TaoFivePrimes.sine_bin_65k_group_08 (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+96))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+96)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+96):ℝ)/10000 := by sorry
