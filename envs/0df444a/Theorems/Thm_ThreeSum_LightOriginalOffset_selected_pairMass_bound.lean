-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalOffset_selected_pairMass_bound
-- name    : ThreeSum.LightOriginalOffset.selected_pairMass_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:06.141273+00:00
-- url     : https://prove2.me/theorems/b180ddd2-7d17-4699-9d1f-f6cfb5d5c3ce
-- title:
--   Light Original Offset: selected pair Mass bound
-- statement:
--   The actual selected offset satisfies the exact raw-incidence mean bound,
--   including duplicate keys in either original array.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L31-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L31-L43

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_ThreeSum_Histograms_selected_pairMass_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.LightOriginalOffset.selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by sorry
