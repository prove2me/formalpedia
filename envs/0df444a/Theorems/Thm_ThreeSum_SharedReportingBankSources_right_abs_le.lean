-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_right_abs_le
-- name    : ThreeSum.SharedReportingBankSources.right_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:46.819871+00:00
-- url     : https://prove2.me/theorems/df34ef42-0eed-4155-afec-e6ead51177a9
-- title:
--   Shared Reporting Bank Sources: right abs le
-- statement:
--   The Shared Reporting Bank Sources construction uses the right abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L50-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L50-L54

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem ThreeSum.SharedReportingBankSources.right_abs_le (p shift : ℤ) (NC g i h J s : ℕ) (fC : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |rightSource p shift (SourceBandPartition.source NC g i) (fun t : Fin NC => fC t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) := by sorry
