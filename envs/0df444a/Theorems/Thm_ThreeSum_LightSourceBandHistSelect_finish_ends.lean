-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandHistSelect_finish_ends
-- name    : ThreeSum.LightSourceBandHistSelect.finish_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:00.645908+00:00
-- url     : https://prove2.me/theorems/e39ba85d-1496-4d13-a298-f193b072dc53
-- title:
--   Light Source Band Hist Select: finish ends
-- statement:
--   The Light Source Band Hist Select construction uses the finish ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L29-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L29-L42

import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHistSelect
open Light BandPartition SourceBandPairData SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandHistSelect.finish_ends {μ : ℕ → ℤ} {pair i dst left right : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : dst+2 ≤ lim.space)
    (hl : left ≤ lim.space) (hr : right ≤ lim.space) :
    Ends lim P d finishBody ⟨frame [pair,i,dst,left,right],μ⟩ 40
      (fun σ => σ.mem dst=(left : ℤ) ∧ σ.mem (dst+1)=(right : ℤ) ∧ Kept μ σ.mem dst) := by sorry
