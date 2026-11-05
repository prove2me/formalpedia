-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPostABI_post_values
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.post_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:55.394346+00:00
-- url     : https://prove2.me/theorems/48b2b700-b1c6-47f6-9f8b-aaa1250a9dd4
-- title:
--   post_values
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L44-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L44-L81

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.post_values {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
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
