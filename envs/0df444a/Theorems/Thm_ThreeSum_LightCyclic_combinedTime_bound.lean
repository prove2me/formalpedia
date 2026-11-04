-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_combinedTime_bound
-- name    : ThreeSum.LightCyclic.combinedTime_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:11.105274+00:00
-- url     : https://prove2.me/theorems/7ba96b36-98b3-4f2e-9659-75f8d165b342
-- title:
--   Light Cyclic: combined Time bound
-- statement:
--   The Light Cyclic construction uses the combined Time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L130-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L130-L133

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.combinedTime_bound (k p : ℕ) (hp : p ≤ 2^k) :
    combinedTime k p ≤ LightKaratsuba.time k + 106 * 2^k + 106 := by sorry
