-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorParameterData_color_reads
-- name    : ThreeSum.EncodedColorParameterData.color_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:36.176089+00:00
-- url     : https://prove2.me/theorems/66f6f91e-f080-47c5-8236-c8ff30f15ef1
-- title:
--   Encoded Color Parameter Data: color reads
-- statement:
--   The Encoded Color Parameter Data construction uses the color reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorParameterData.lean#L30-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorParameterData.lean#L30-L42

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorParameterData
open Light Scales BandScales

theorem ThreeSum.EncodedColorParameterData.color_reads {μ : ℕ → ℤ} {row W : ℕ} {color : Coloring.Parameter W}
    (H : Seg μ row (ColorParameters.fields color)) :
    μ row=(color.1.1.val : ℤ) ∧ μ (row+1)=(color.1.2.val : ℤ) ∧
    μ (row+2)=((color.2 (false,false)).val : ℤ) ∧ μ (row+3)=((color.2 (false,true)).val : ℤ) ∧
    μ (row+4)=((color.2 (true,false)).val : ℤ) ∧ μ (row+5)=((color.2 (true,true)).val : ℤ) := by sorry
