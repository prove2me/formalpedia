-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_mem_positions
-- name    : ThreeSum.SourceBandData.At.mem_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:47.223863+00:00
-- url     : https://prove2.me/theorems/15e34b93-5082-46fd-b66d-97b5bdc704ca
-- title:
--   At: mem positions
-- statement:
--   The At construction uses the mem positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L88-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L88-L106

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.mem_positions {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i r t : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hg : 0 < g)
    (hi : i < size n g) (hr : r < m) :
    t ∈ positions μ base n g m i r ↔
      start g i ≤ t ∧ t < stop n g i ∧ LightSourceResidues.key p m shift (f t)=r := by sorry
