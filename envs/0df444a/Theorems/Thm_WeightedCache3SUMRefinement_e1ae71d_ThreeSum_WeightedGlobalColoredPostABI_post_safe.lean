-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPostABI_post_safe
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.post_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:53:38.583184+00:00
-- url     : https://prove2.me/theorems/b18abea7-183d-41d4-a14b-387f037a0f6f
-- title:
--   post_safe
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L136-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L136-L170

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.post_safe {lim : Limits} (loc μ : ℕ→ℤ)
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
