-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
-- name    : ThreeSum.LightWeightedGlobalControllerFactory.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:18:16.953549+00:00
-- url     : https://prove2.me/theorems/70342fe4-a78a-48de-a5ec-e08ece0654c1
-- title:
--   Light Weighted Global Controller Factory: run
-- statement:
--   A pure state invariant, concrete candidate guards, and the actual span
--   layout derive all operational premises of the finite menu controller.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L144-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L144-L201

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalControllerFactory.run {C : Config} [Fact C.p.Prime] (D : Family C) {lim : Limits}
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
