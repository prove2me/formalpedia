-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
-- name    : ThreeSum.LightReportingSuffixSum.partialSum_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:26:50.446194+00:00
-- url     : https://prove2.me/theorems/5bf05083-6d13-4dd2-b5f6-7072957c2221
-- title:
--   Light Reporting Suffix Sum: partial Sum length
-- statement:
--   The Light Reporting Suffix Sum construction uses the partial Sum length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSum.lean#L30-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSum.lean#L30-L38

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixSum.partialSum_length {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) :
    partialSum hfit Q preL preR f g stage missing missing.length =
      (missing.map (term hfit Q preL preR f g stage)).sum := by sorry
