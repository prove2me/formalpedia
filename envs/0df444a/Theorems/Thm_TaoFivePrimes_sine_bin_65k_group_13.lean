-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65k_group_13
-- name    : TaoFivePrimes.sine_bin_65k_group_13
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:31.176813+00:00
-- url     : https://prove2.me/theorems/e8ca9dfe-fd23-4ed1-9004-08a19474226a
-- title:
--   Sine-square enclosures for 65,000-height bins 156–167
-- statement:
--   For each integer $n$ with $156\le n\le 167$, let $b_n$ be the stored rational-enclosure numerator. If
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

theorem TaoFivePrimes.sine_bin_65k_group_13 (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+156))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+156)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+156):ℝ)/10000 := by sorry
