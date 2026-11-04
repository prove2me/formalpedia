-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_left_abs_le
-- name    : ThreeSum.SharedReportingBankSources.left_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:25.499194+00:00
-- url     : https://prove2.me/theorems/32235bd0-9177-44dd-8069-901b80870ac5
-- title:
--   Shared Reporting Bank Sources: left abs le
-- statement:
--   The Shared Reporting Bank Sources construction uses the left abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L44-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L44-L48

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem ThreeSum.SharedReportingBankSources.left_abs_le (p : ℤ) (NB g i h J s : ℕ) (fB : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) := by sorry
