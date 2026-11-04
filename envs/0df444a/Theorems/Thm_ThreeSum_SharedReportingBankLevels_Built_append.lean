-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankLevels_Built_append
-- name    : ThreeSum.SharedReportingBankLevels.Built.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:20:27.3148+00:00
-- url     : https://prove2.me/theorems/cc647095-e6ba-4b9b-a2bf-3740acabd9d3
-- title:
--   Built: append
-- statement:
--   The Built construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L119-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean#L119-L134

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000

theorem ThreeSum.SharedReportingBankLevels.Built.append {μ ν : ℕ → ℤ} {record base h J i : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Built μ record base h J i f g)
    (hi : i ≤ J)
    (Hnew : Entry ν (record+5*i) (catalogAt base h J i) hi f g)
    (hkeep : KeptBut μ ν (baseAt base h J i) (record+5*i) 5)
    (hrecord : record+5*i+5 ≤ base) : Built ν record base h J (i+1) f g := by sorry
