-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_call_total
-- name    : ThreeSumSharpTail.full_d_call_total
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:11:15.788791+00:00
-- url     : https://prove2.me/theorems/6ea522e3-51f4-495c-a590-edd3b31d37e7
-- title:
--   All full dimension oracle calls have the desired saving
-- statement:
--   Under the full-D parameter bounds and D^(1+s)<=n, a call with preprocessing n^2(log D+1)^2/D^s, query time D^(1/2-s)(log D+1), and nD+w+1 overhead, with w<=n^2/sqrt(D), has total 4ng call-and-answer-reading cost at most (64C+8Cprime)n^3 D^(-s/2)(log D+1)^2. Both cost constants are nonnegative and all loop overheads are counted.
-- source:
--   Derived elementary full-D runtime inequality for Xu, same manuscript, Sections 3-4; uses the proved full_d_call_balance.

import Mathlib
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.full_d_call_total (n D g s C C' t w : ℝ)
    (hD : 1 ≤ D) (hn : 1 ≤ n) (hs : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (_hw0 : 0 ≤ w) (hw : w ≤ n ^ 2 / Real.sqrt D)
    (ht : t ≤ C *
      (n ^ 2 * (Real.log D + 1) ^ 2 / D ^ s +
        w * D ^ (1 / 2 - s) * (Real.log D + 1) + n * D + w + 1)) :
    4 * n * g * (t + C' * n ^ 2 / Real.sqrt D) ≤
      (64 * C + 8 * C') *
        (n ^ 3 * D ^ (-s / 2) * (Real.log D + 1) ^ 2) := by sorry
