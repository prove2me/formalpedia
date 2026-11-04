-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalSolver_meets
-- name    : ThreeSum.WeightedGlobalArenaFinalSolver.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:26:55.487995+00:00
-- url     : https://prove2.me/theorems/67c16bc1-6e3a-42ab-9d8e-527bb2b83fc0
-- title:
--   Weighted Global Arena Final Solver: meets
-- statement:
--   The closed actual final solver, including histogram construction, original
--   collision cleanup, real compaction, all signed channels and determinant detection.
--   No execution callback or semantic source/correctness certificate is an input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalSolver.lean#L22-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalSolver.lean#L22-L78

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
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
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47
import Theorems.Thm_ThreeSum_LightReportingGather_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryFinalPreparation_meets
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalRequester_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPhysicalMomentBatch_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
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
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalCompactReporter_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentChannelFactory_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_meets
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

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalSolver
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection WeightedGlobalArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalSolver.meets {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim (d+1) M n U Hdet I.nB I.nC)
    (R : LightWeightedGlobalPreparedPostSelection.Inputs
      (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim (d+2) U L μ A B C keysB keysC)
    (Meta : WeightedGlobalArenaPostMemory.Metadata (r := r) maps τ
      (selectedInput I U radix nA H A B C keysB keysC) μ)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA,|A i|≤(U : ℤ)) (hB : ∀j<I.nB,|B j|≤(U : ℤ))
    (hC : ∀j<I.nC,|C j|≤(U : ℤ))
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hkB : ∀j<I.nB,keysB j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC,keysC j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight H U radix (C j)))
    (hsupport : 2*p^K≤Hdet)
    (hzero : WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)) K J
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.leftRaw U radix J (B j)) i)
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix J (C j)) i)=0) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    let c := WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
    Meets lim (LightWeightedGlobalPreparedPostSelection.program S Hdet)
      (LightWeightedGlobalPreparedPostSelection.libraries S Hdet).length d
      (LightWeightedGlobalPreparedPostSelection.args S c (addr I.free I.capacity 26) (addr I.free I.capacity 25)) μ
      (LightWeightedGlobalPreparedPostSelection.time S Hdet c keysB keysC)
      (fun ret ν => ret=(if ∃i<nA,∃j<I.nB,∃k<I.nC,C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept μ ν (addr I.free I.capacity 6)) := by sorry
