-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyOffset_pairMass_eq_wantedCount
-- name    : ThreeSum.GlobalKeyOffset.pairMass_eq_wantedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:39.787577+00:00
-- url     : https://prove2.me/theorems/c9b41c15-9222-4068-8d2d-bc2ce5256f9b
-- title:
--   Global Key Offset: pair Mass eq wanted Count
-- statement:
--   The Global Key Offset construction uses the pair Mass eq wanted Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L38-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyOffset.lean#L38-L51

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyOffset.pairMass_eq_wantedCount (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) (d : ℤ) :
    Histograms.pairMass (Finset.range left.length) (Finset.range (globalKeys h J).length)
      (fun i => (left.getD i 0 : ZMod p))
      (fun i => ((globalKeys h J).getD i 0 : ZMod p))
      (fun _ => 1) (fun _ => 1) (d : ZMod p) = wantedCount p left h J d := by sorry
