-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_eq_7
-- name    : SampleCRS.AlmostGreedy.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:40.542257+00:00
-- url     : https://prove2.me/theorems/8db873b1-1fad-4a44-adc7-3d0e47518152
-- title:
--   §4.1, equation (7): every case of the discrete difference
-- statement:
--   For every integer capacity $k\ge1$ and nonnegative integer $s$,
--   $$h_k(s+1)-h_k(s)=\begin{cases}\frac1{2k+1},&0\le s\le k-2,\\0,&s=k-1,\\-\frac{k(k+1)}{(2k+1)(s+1)(s+2)},&s\ge k.\end{cases}$$
--
--   The positive, zero and negative cases describe the shape of $h_k$ on the entire count domain. The first case is empty when $k=1$; the remaining two cases still apply.
--
--   Differences from the source:
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: the first case 0 ≤ s ≤ k−2 → s : ℕ with an integer inequality s ≤ k−2; reason: natural s enforces the lower bound without truncating the upper bound
--   - encoding: the third case s ≥ k → the final branch after excluding the first two cases; reason: for k ≥ 1 and s ≥ 0 these exclusions are exactly s ≥ k
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, eq. (7), p.17

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- All three cases of equation (7), p.17. The first interval is empty at k=1. -/
theorem eq_7 (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    h k (s + 1) - h k s =
      if (s : ℤ) ≤ (k : ℤ) - 2 then 1 / (2 * (k : ℝ) + 1)
      else if s = k - 1 then 0
      else -((k : ℝ) * ((k : ℝ) + 1)) /
        ((2 * (k : ℝ) + 1) * ((s : ℝ) + 1) * ((s : ℝ) + 2)) := by sorry

end SampleCRS.AlmostGreedy
