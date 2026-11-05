-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalPreludeResources_need_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.need_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:47:16.897485+00:00
-- url     : https://prove2.me/theorems/6412d979-66c8-431a-8803-948cb585bc68
-- title:
--   need_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L24-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L24-L50

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.need_meets {lim : Limits} {M b p K κ n U free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (H : (need M b p K κ n U).Ok lim free depth) :
    Meets lim (program M b p K κ) 49 depth [n,free] μ
      (LightWeightedGlobalGlobalPreludeProof.time M b p K κ n free)
      (fun z ν=>∃c<p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)), z=(free:ℤ) ∧
        Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) c) ∧
        Seg ν free (header n (n^κ) (LightWeightedGlobalDimensions.r M n)
          (LightWeightedGlobalDimensions.J M b n (n^κ)) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
          (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) free c) ∧
        Seg ν (params free) (LightScales.values n) ∧
        LightWeightedGlobalGlobalPreludeProof.Menu ν (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
          (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ)) c ∧
        Kept μ ν free) := by sorry
