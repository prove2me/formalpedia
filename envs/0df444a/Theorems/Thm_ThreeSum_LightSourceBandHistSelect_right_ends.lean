-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandHistSelect_right_ends
-- name    : ThreeSum.LightSourceBandHistSelect.right_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:50.857427+00:00
-- url     : https://prove2.me/theorems/6910169c-93e0-4785-a041-e4d476ceb623
-- title:
--   Light Source Band Hist Select: right ends
-- statement:
--   The Light Source Band Hist Select construction uses the right ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L44-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L44-L87

import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHistSelect
open Light BandPartition SourceBandPairData SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandHistSelect.right_ends {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst left : ℕ} {shift : ℤ}
    (H : Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) (hl : left ≤ lim.space) :
    Ends lim P d rightBody
      ⟨frame [pair,i,dst,left,zeroBase pair NL NR g m],μ⟩ 200
      (fun σ => σ.mem dst=(left : ℤ) ∧
        σ.mem (dst+1)=(histRight pair NL NR g m i : ℤ) ∧ Kept μ σ.mem dst) := by sorry
