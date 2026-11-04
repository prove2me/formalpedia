-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_coordinates_injective
-- name    : ThreeSum.BandRawA.coordinates_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:49.831841+00:00
-- url     : https://prove2.me/theorems/384a8f89-8801-4bcc-916a-403a5c14f602
-- title:
--   Band Raw A: coordinates injective
-- statement:
--   The Band Raw A construction uses the coordinates injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L38-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L38-L42

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by sorry
