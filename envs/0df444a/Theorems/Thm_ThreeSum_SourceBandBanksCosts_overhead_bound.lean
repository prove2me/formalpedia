-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_overhead_bound
-- name    : ThreeSum.SourceBandBanksCosts.overhead_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:22:37.096482+00:00
-- url     : https://prove2.me/theorems/cf06eac6-0116-48bd-b219-f170b179e7dd
-- title:
--   Source Band Banks Costs: overhead bound
-- statement:
--   The Source Band Banks Costs construction uses the overhead bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L77-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L77-L83

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.overhead_bound (h J : ℕ) : LightBlockSourceRetainedHost.space 0 h J ≤
    J+2*(J*(512*h))+(J*(512*h)+1)^2+
      Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+20 := by sorry
