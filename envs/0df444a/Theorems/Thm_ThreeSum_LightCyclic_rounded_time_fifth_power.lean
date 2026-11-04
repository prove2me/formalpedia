-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_rounded_time_fifth_power
-- name    : ThreeSum.LightCyclic.rounded_time_fifth_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:20.639708+00:00
-- url     : https://prove2.me/theorems/46682f24-e9d5-48ab-96ea-e771f0b115ba
-- title:
--   Light Cyclic: rounded time fifth power
-- statement:
--   The Light Cyclic construction uses the rounded time fifth power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L164-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L164-L169

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_time_fifth_power

set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.rounded_time_fifth_power {p : ℕ} (hp : 0 < p) :
    combinedTime (Nat.clog 2 p) p ^ 5 ≤
      ((2530+2*106)^5 * 2^8) * p^8 := by sorry
