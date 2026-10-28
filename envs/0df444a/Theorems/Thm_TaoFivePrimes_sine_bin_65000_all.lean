-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_bin_65000_all
-- name    : TaoFivePrimes.sine_bin_65000_all
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:04:27.094901+00:00
-- url     : https://prove2.me/theorems/7d7759ca-1c09-43fb-8959-b15321e6793d
-- title:
--   Sine-square bounds for all 180 height bins
-- statement:
--   For $0\le n<180$, let $b_n$ be the stored integer and put $L_n=65000+1290n$ and $U_n=L_n+1290$. If
--
--   $$
--   \frac{L_n}{4302}\le x\le\frac{U_n}{4298},
--   $$
--
--   then $\sin^2 x\le b_n/10000$. This unifies the fifteen separately verified groups of twelve interval enclosures.
-- source:
--   Combines the independently checked grouped certificates for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

theorem TaoFivePrimes.sine_bin_65000_all (i : Fin 180) (x : ℝ)
    (hx0 : (65000+1290*(i.val:ℝ))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*(i.val:ℝ)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000 := by sorry
