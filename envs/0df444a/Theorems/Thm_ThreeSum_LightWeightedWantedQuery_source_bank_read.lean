-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedWantedQuery_source_bank_read
-- name    : ThreeSum.LightWeightedWantedQuery.source_bank_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:23:02.635345+00:00
-- url     : https://prove2.me/theorems/42865f30-8b35-4e1e-bc58-f47d5721f408
-- title:
--   Light Weighted Wanted Query: source bank read
-- statement:
--   The source values required by Euler reconstruction are exactly the final
--   forward-stage cells produced by the bank assembler.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L126-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L126-L131

import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_WantedQuery
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedWantedQuery.source_bank_read {N T n base : ℕ} (E : Enumeration N T n)
    (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightWeightedBankSweep.Stages E (fun k => forwardStage k F) base N μ) :
    ∀ j<n, μ (base+N*n+j)=ThreeSum.TernaryEuler.binomialZeta F (E.word j) := by sorry
