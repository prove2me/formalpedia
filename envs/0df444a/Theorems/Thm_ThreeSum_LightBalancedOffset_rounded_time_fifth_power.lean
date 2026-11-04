-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedOffset_rounded_time_fifth_power
-- name    : ThreeSum.LightBalancedOffset.rounded_time_fifth_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:55.762875+00:00
-- url     : https://prove2.me/theorems/5bbae7d0-0178-488e-8ae1-8d60d5e043a3
-- title:
--   Light Balanced Offset: rounded time fifth power
-- statement:
--   The Light Balanced Offset construction uses the rounded time fifth power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L109-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L109-L112

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_time_fifth_power
import Theorems.Thm_ThreeSum_LightCyclic_rounded_time_fifth_power

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBalancedOffset.rounded_time_fifth_power {p : ℕ} (hp : 0 < p) :
    time (Nat.clog 2 p) p ^ 5 ≤ ((2530+2*226)^5*2^8)*p^8 := by sorry
