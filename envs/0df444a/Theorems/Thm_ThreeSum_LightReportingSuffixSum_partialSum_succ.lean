-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_succ
-- name    : ThreeSum.LightReportingSuffixSum.partialSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:26:51.787816+00:00
-- url     : https://prove2.me/theorems/6e2c07b6-5b26-40cf-af59-f15986d07062
-- title:
--   Light Reporting Suffix Sum: partial Sum succ
-- statement:
--   The Light Reporting Suffix Sum construction uses the partial Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSum.lean#L22-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSum.lean#L22-L28

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_succ
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_succ

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixSum.partialSum_succ {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) {j : ℕ} (hj : j < missing.length) :
    partialSum hfit Q preL preR f g stage missing (j+1) =
      partialSum hfit Q preL preR f g stage missing j+term hfit Q preL preR f g stage missing[j] := by sorry
