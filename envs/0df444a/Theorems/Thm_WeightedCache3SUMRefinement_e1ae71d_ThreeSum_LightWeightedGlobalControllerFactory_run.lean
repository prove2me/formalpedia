-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_run
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:29:11.710129+00:00
-- url     : https://prove2.me/theorems/3bbd094f-2d59-45b8-889d-e85f7c57dd6b
-- title:
--   run
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L144-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L144-L201

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory.run {C : Config} [Fact C.p.Prime] (D : Family C) {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ)
    (I : ℕ→(ℕ→ℤ)→Prop) (Replay Final : (ℕ→ℤ)→Prop)
    (hw : (lim.space:ℤ)≤lim.word)
    (hFlags : C.flags+n≤lim.space) (hBs : C.scoreB+n≤lim.space)
    (hCs : C.scoreC+n≤lim.space) (hPs : C.scorePaired+n≤lim.space)
    (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP:ℤ)≤lim.word)
    (hLen : C.J+2≤lim.space)
    (hRow : C.menu+(D.pick K n dB dC dP tB tC tP-1)*(C.J+2)≤lim.space)
    (hd : depth<lim.depth) (hstart : I 0 μ)
    (hguard : ∀i<n, ∀ν, I i ν→(D.candidate i).Guard lim (depth+1) K R S raws words maps ν)
    (htime : ∀i<n, (D.candidate i).runtime K R S raws words maps≤seedTime)
    (hnext : ∀i<n, ∀ν ξ, I i ν→(D.candidate i).Done K ν ξ→I (i+1) ξ)
    (hread : ∀ν, I n ν→
      (∀i<n, ν (C.flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
      (∀i<n, ν (C.scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
      (∀i<n, ν (C.scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
      (∀i<n, ν (C.scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U))
    (hexist : ∃i<n, LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
      dB dC dP tB tC tP i)
    (hreplayGuard : ∀ν, I n ν→
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).Guard lim (depth+1) K R S raws words maps ν)
    (hreplay : ∀ν ξ, I n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).Done K ν ξ→Replay ξ)
    (hspan : ∀ν, Replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν)
    (hfinal : ∀ν ξ, Replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→Final ξ) :
    Meets lim (LightWeightedGlobalSeedController.program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr)
      178 depth (LightWeightedGlobalSeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan)
      μ (LightWeightedGlobalSeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows))
      (fun r ν=>r=(D.pick K n dB dC dP tB tC tP:ℤ) ∧ Final ν) := by sorry
