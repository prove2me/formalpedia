-- Prove2me | Theorems.Thm_ThreeSum_LightArray_linear_output_segment
-- name    : ThreeSum.LightArray.linear_output_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:19.85151+00:00
-- url     : https://prove2.me/theorems/81002796-4936-45fd-9d5f-79ba95ff707d
-- title:
--   Light Array: linear output segment
-- statement:
--   Turn the per-cell execution postcondition into an ordinary segment
--   specification, without treating arbitrary function evaluation as a machine op.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L90-L97

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightArray.linear_output_segment {μ μ' : ℕ → ℤ} {srcA srcB dst n : ℕ}
    {c : ℤ} {as bs : List ℤ} (hA : Seg μ srcA as) (hB : Seg μ srcB bs)
    (hlenA : as.length = n) (hlenB : bs.length = n)
    (hout : ∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) :
    Seg μ' dst (List.zipWith (fun a b => a + c * b) as bs) := by sorry
