-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedQuery_source_bank_read
-- name    : ThreeSum.LightTernaryWantedQuery.source_bank_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:59.529787+00:00
-- url     : https://prove2.me/theorems/1f658662-08dd-4394-8a43-6cae936bae7c
-- title:
--   Light Ternary Wanted Query: source bank read
-- statement:
--   The source values required by Euler reconstruction are exactly the final
--   forward-stage cells produced by the bank assembler.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L116-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L116-L121

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedQuery.source_bank_read {N T n base : ℕ} (E : Enumeration N T n)
    (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightTernaryBankSweep.Stages E (fun k => forwardStage k F) base N μ) :
    ∀ j<n, μ (base+N*n+j)=ThreeSum.TernaryEuler.binomialZeta F (E.word j) := by sorry
