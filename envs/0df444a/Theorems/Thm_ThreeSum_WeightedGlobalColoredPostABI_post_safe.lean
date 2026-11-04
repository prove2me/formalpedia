-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_post_safe
-- name    : ThreeSum.WeightedGlobalColoredPostABI.post_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:10:02.094198+00:00
-- url     : https://prove2.me/theorems/1c9e5e16-b839-44f1-ae6a-5e00f0180389
-- title:
--   Weighted Global Colored Post ABI: post safe
-- statement:
--   The Weighted Global Colored Post ABI construction uses the post safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L136-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L136-L170

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.post_safe {lim : Limits} (loc μ : ℕ→ℤ)
    (header host free capacity aBase nA bBase nB cBase nC q L : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(free : ℤ))
    (hloc7 : loc 7=(capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,nB,cBase,nC])
    (hheaderSpace : header+6≤lim.space) (hhostSpace : host+106≤lim.space)
    (hcapacity : 106≤capacity) (hend : finish free capacity≤lim.space)
    (hcounts : nB+3*nC+1≤capacity)
    (ha : aBase≤lim.space) (hna : nA≤lim.space)
    (hb : bBase≤lim.space) (hc : cBase≤lim.space)
    (hq : q≤lim.space) (hL : L≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) : ∀e∈postArgs,e.Safe lim ⟨loc,μ⟩ := by sorry
