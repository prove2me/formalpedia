-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaMomentResources_weight_bounds
-- name    : ThreeSum.WeightedGlobalArenaMomentResources.weight_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:48:19.801797+00:00
-- url     : https://prove2.me/theorems/6358a711-99d1-4b46-b6b8-bf0f92b3a289
-- title:
--   Weighted Global Arena Moment Resources: weight bounds
-- statement:
--   The Weighted Global Arena Moment Resources construction uses the weight bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L44-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L44-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaMomentResources.weight_bounds (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (B C : ℕ→ℤ) (U K : ℕ)
    (hB : ∀ i<I.nB, |B i|≤(U : ℤ)) (hC : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hcap : leftBound U K≤I.weightCap) :
    ∀ k<K+1, ∀ j≤k,
      (∀ i<(setup (r := r) maps τ cap Q I).left.NL,
        |LightWeightedGlobalMomentChannelFactory.leftWeights k j B i|≤
          ((setup (r := r) maps τ cap Q I).left.weightU : ℤ)) ∧
      (∀ i<(setup (r := r) maps τ cap Q I).right.NL,
        |LightWeightedGlobalMomentChannelFactory.rightWeights k j C i|≤
          ((setup (r := r) maps τ cap Q I).right.weightU : ℤ)) := by sorry
