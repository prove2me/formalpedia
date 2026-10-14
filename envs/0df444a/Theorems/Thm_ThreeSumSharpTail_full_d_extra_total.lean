-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_extra_total
-- name    : ThreeSumSharpTail.full_d_extra_total
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:11:19.505297+00:00
-- url     : https://prove2.me/theorems/82d81272-5461-43d6-a2ad-99bbc5f46c95
-- title:
--   Full dimension scan, prime and construction costs preserve the saving
-- statement:
--   For n>=3, 1<=D<=n^a, 0<=s<=1/2, D^(s/2)<=g<=2D^(s/2), a(1+s)<=1 and log_2(7)+3a/2<=3-as/2, the actual scan, prime-selection and instance-construction time functions of the full-D host are bounded by 4C kappa n^3 D^(-s/2) log^2 n whenever C>=0 and kappa>=1.
-- source:
--   Derived bound for the actual termScans, termPrime and termBuild functions in the pinned full-D Theorem 17 interface. The certificate strict prime/build margins imply its hypotheses.

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
import Mathlib
open ThreeSumApsp

theorem ThreeSumSharpTail.full_d_extra_total (n D g : ℕ) (a s κ C : ℝ)
    (hn : 3 ≤ n) (hD : 1 ≤ D) (hDa : (D : ℝ) ≤ (n : ℝ) ^ a)
    (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : (D : ℝ) ^ (s / 2) ≤ g) (hgHi : (g : ℝ) ≤ 2 * (D : ℝ) ^ (s / 2))
    (hbuild : a * (1 + s) ≤ 1)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hκ : 1 ≤ κ) (hC : 0 ≤ C) :
    C * (termScans n g κ + termPrime strassen n D + termBuild n D g) ≤
      4 * C * (κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) * Real.log n ^ 2)) := by sorry
