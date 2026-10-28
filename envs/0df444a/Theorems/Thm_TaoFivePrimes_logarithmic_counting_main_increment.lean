-- Prove2me | Theorems.Thm_TaoFivePrimes_logarithmic_counting_main_increment
-- name    : TaoFivePrimes.logarithmic_counting_main_increment
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:45:55.121107+00:00
-- url     : https://prove2.me/theorems/cf73ddf3-846b-4c85-9ccd-59b2b531db76
-- title:
--   An upper bound for a logarithmic counting-main increment
-- statement:
--   Let $0<H\le t$ and $c>0$. Then
--
--   $$
--   \frac{t}{c}\left(\log\frac{t}{c}-1\right)
--   -\frac{H}{c}\left(\log\frac{H}{c}-1\right)
--   \le \frac{t-H}{c}\log\frac{t}{c}.
--   $$
--
--   In particular, taking $c=2\pi$ bounds the main-term increment in the Riemann–von Mangoldt zero count by the length of the interval times its upper-endpoint logarithmic density.
-- source:
--   Elementary logarithmic inequality used with the published Riemann–von Mangoldt counting main term; derived using log x ≤ x−1 for x>0.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem TaoFivePrimes.logarithmic_counting_main_increment
    (H t c : ℝ) (hH : 0 < H) (hHt : H ≤ t) (hc : 0 < c) :
    t/c * (Real.log (t/c)-1) - H/c * (Real.log (H/c)-1) ≤
      (t-H)/c * Real.log (t/c) := by sorry
