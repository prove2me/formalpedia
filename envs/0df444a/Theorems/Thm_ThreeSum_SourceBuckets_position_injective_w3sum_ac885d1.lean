-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_injective_w3sum_ac885d1
-- name    : ThreeSum.SourceBuckets.position_injective_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:08.239111+00:00
-- url     : https://prove2.me/theorems/55a2907b-acc7-4b95-89e8-7304b34e5abe
-- title:
--   Source Buckets: position injective
-- statement:
--   The Source Buckets construction uses the position injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L76-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean#L76-L93

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem ThreeSum.SourceBuckets.position_injective_w3sum_ac885d1 {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hj : j < N) (he : position key N i = position key N j) : i = j := by sorry
