-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPostCertificate_certificate
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostCertificate.certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:40.211503+00:00
-- url     : https://prove2.me/theorems/b911ba8b-da52-44ca-b3ea-e85bfd611869
-- title:
--   certificate
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostCertificate.lean#L52-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostCertificate.lean#L52-L130

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostCertificate
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostCertificate.certificate {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim d M n U Hdet I.nB I.nC)
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
    Certificate (setup (r := r) maps τ cap Q I')
      (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim d Hdet (r*alphaRank m) (r*alphaRank m) U
      (WeightedGlobalMomentChannelResources.scoreBound (WeightedGlobalArenaPairMass.envelope maps cap M n) U (2*Hdet))
      (WeightedGlobalMomentDetectorResources.input (WeightedGlobalArenaPairMass.envelope maps cap M n) U Hdet)
      (addr I.free I.capacity 26) (addr I.free I.capacity 25)
      μ A B C keysB keysC (WeightedGlobalArenaNativeComplete.originalPosition (r := r) maps τ I') := by sorry
