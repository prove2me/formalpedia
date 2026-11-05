-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaMomentResources_weight_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources.weight_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:33:35.485732+00:00
-- url     : https://prove2.me/theorems/a621a6f3-bcee-43c7-be07-9b00c0eff333
-- title:
--   weight_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L44-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L44-L64

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_bounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources.weight_bounds (maps : Fin F→Weight m p) (τ cap : ℕ)
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
