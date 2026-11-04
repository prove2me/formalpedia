-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredFinalCall_final_call
-- name    : ThreeSum.WeightedGlobalColoredFinalCall.final_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:15:24.067077+00:00
-- url     : https://prove2.me/theorems/f6d0b58a-47a6-497c-8b5d-1f858e355098
-- title:
--   Weighted Global Colored Final Call: final call
-- statement:
--   The Weighted Global Colored Final Call construction uses the final call property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinalCall.lean#L19-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinalCall.lean#L19-L94

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection WeightedGlobalArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalColoredFinalCall.final_call {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim (d+2) M n U Hdet I.nB I.nC)
    (R : LightWeightedGlobalPreparedPostSelection.Inputs
      (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim (d+3) U L μ A B C keysB keysC)
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
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix J (C j)) i)=0)
    (pre suffix : Program) (loc : ℕ→ℤ) (header host : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(I.free : ℤ))
    (hloc7 : loc 7=(I.capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,I.nB,cBase,I.nC])
    (hheaderSpace : header+6≤lim.space) (hhostSpace : host+106≤lim.space)
    (hcapacity : 106≤I.capacity)
    (hhost : ∀i<106,i≠11→i≠34→μ (host+i)=
      (LightWeightedGlobalCompactReporter.zeroCounts (setup (r := r) maps τ cap Q
        (selectedInput I U radix nA H A B C keysB keysC))).argv.getD i 0) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    let c := WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
    let post := LightWeightedGlobalPreparedPostSelection.closedProgram
      S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs Hdet
    Ends lim (ReportingHostRelocation.program pre post++suffix) d
      (.call (pre.length+(139*(TernaryMomentSchedule.channels (2*Hdet+1)).length+24))
        LightWeightedGlobalColoredSolver.postArgs 0) ⟨loc,μ⟩
      ((LightWeightedGlobalColoredSolver.postArgs.map Expr.cost).sum+2+
        LightWeightedGlobalPreparedPostSelection.time S Hdet c keysB keysC)
      (fun σ=>σ.loc 0=(if ∃i<nA,∃j<I.nB,∃k<I.nC,C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept μ σ.mem (addr I.free I.capacity 6)) := by sorry
