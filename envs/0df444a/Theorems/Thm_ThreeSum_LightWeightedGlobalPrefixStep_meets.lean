-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixStep_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixStep.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:52:05.8972+00:00
-- url     : https://prove2.me/theorems/64155aad-8802-4bfa-9b95-fc52fd181698
-- title:
--   Light Weighted Global Prefix Step: meets
-- statement:
--   Entry 192 runs all real preparation, scan/replay, key commits, and span
--   commit. The controller plans are pure certificates, not execution callbacks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixStep.lean#L104-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixStep.lean#L104-L132

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_meets
import Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryBudgetStep_meets
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRepeatWord_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryTensorScatter_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentChannelFactory_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPrepare_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalQuarticStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixStep
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixStep.meets {X : Inputs} {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    {raws : List ℤ} {words maps : List ℕ} (μ : ℕ→ℤ)
    (H : PrepareReady X lim (depth+1) μ)
    (hprime : X.p=C.p) (hJ : X.J=C.J)
    (plans : ∀ν, Prepared X μ ν→FullPlan C D lim (depth+1) K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps ν)
    (A : LightWeightedGlobalPrefixFinish.Layout C lim X.seed (X.power*X.p) newSpan)
    (hheader : ∀ν, Prepared X μ ν→Seg ν X.seed (LightWeightedGlobalPrefixFinish.header C n dB dC dP tB tC tP newSpan))
    (hfinal : ∀ν, ∀h : Prepared X μ ν, ∀ξ, (plans ν h).finalState ξ→
      Seg ξ X.seed (LightWeightedGlobalPrefixFinish.header C n dB dC dP tB tC tP newSpan)) :
    Meets lim (program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr) 192 depth X.argv μ (time X C n seedTime)
      (fun r ω=>r=((X.power*X.p:ℕ):ℤ) ∧ ∃ν, ∃h : Prepared X μ ν, ∃ξ,
        (plans ν h).finalState ξ ∧ LightWeightedGlobalPrefixFinish.Committed C (X.power*X.p) newSpan ξ ω ∧
        Seg ω X.seed (LightWeightedGlobalPrefixFinish.header C n dB dC dP tB tC tP newSpan)) := by sorry
