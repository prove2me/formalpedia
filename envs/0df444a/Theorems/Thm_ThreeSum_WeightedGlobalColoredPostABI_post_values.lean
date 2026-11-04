-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_post_values
-- name    : ThreeSum.WeightedGlobalColoredPostABI.post_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:09:49.0681+00:00
-- url     : https://prove2.me/theorems/92d41911-923d-4f2d-ae07-448d5521cfc1
-- title:
--   Weighted Global Colored Post ABI: post values
-- statement:
--   The nineteen-field preparation header is read literally at the final
--   call site; only its first six fields are needed by the final ABI.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L44-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L44-L81

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.post_values {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (loc μ : ℕ→ℤ) (header host free capacity aBase nA bBase nB cBase nC q L : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(free : ℤ))
    (hloc7 : loc 7=(capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,nB,cBase,nC])
    (hhost : ∀ i<106,i≠11→i≠34→
      μ (host+i)=(LightWeightedGlobalCompactReporter.zeroCounts S).argv.getD i 0)
    (hrecords : S.front.records=addr free capacity 19)
    (hweightsB : S.left.weightBase=addr free capacity 28)
    (hweightsC : S.right.weightBase=addr free capacity 29)
    (houtput : S.front.dst=addr free capacity 53) :
    postArgs.map (fun e=>e.val ⟨loc,μ⟩)=
      LightWeightedGlobalPreparedPostSelection.args S
        (WeightedGlobalArenaCleanupLayout.layout free capacity aBase nA bBase nB cBase nC q L)
        (addr free capacity 26) (addr free capacity 25) := by sorry
