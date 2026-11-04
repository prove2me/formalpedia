-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_Done_append_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankRows.Done.append_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:28:22.348709+00:00
-- url     : https://prove2.me/theorems/b581a206-1ea0-4166-bf87-d6e405507841
-- title:
--   Done: append
-- statement:
--   The Done construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L130-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L130-L158

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_BandRawA_Stored_append
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_Built_append

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.Done.append_w3sum_ac885d1 {μ ν : ℕ → ℤ} {record base h J K NB NC g s i j q : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Done μ record base h J K NB NC g q fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g)
    (hq : q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)
    (Hnew : Built ν (rowRecord record K q) (rowBase base h J K q) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s)))
    (heq : KeptBut μ ν (rowBase base h J K q) (rowRecord record K q) (5*K))
    (hslab : record+5*K*total h J NB NC g ≤ base) :
    Done ν record base h J K NB NC g (q+1) fB fC p shift := by sorry
