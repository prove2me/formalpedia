-- Prove2me | Theorems.Thm_ThreeSum_ModuloCosts_time_bound_w3sum_ac885d1
-- name    : ThreeSum.ModuloCosts.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:02.59436+00:00
-- url     : https://prove2.me/theorems/0519fab3-2372-4d1e-9f8a-1fafe780b77e
-- title:
--   Modulo Costs: time bound
-- statement:
--   The Modulo Costs construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCosts.lean#L24-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCosts.lean#L24-L41

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface

theorem ThreeSum.ModuloCosts.time_bound_w3sum_ac885d1 (p nA nB nC N U : ℕ)
    (ha : nA ≤ N) (hb : nB ≤ N) (hc : nC ≤ N) :
    LightModuloCounts.time p nA nB nC U ≤
      10000 * (roundedPower p + N*(Nat.log 2 (U+1)+1) + 1) := by sorry
