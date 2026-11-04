-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairRestriction_embed_injective
-- name    : ThreeSum.WeightedGlobalArenaPairRestriction.embed_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:59:08.271256+00:00
-- url     : https://prove2.me/theorems/3de15a68-fdad-4787-b5f8-64c31d3ce8c2
-- title:
--   Weighted Global Arena Pair Restriction: embed injective
-- statement:
--   The Weighted Global Arena Pair Restriction construction uses the embed injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairRestriction.lean#L51-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairRestriction.lean#L51-L76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairRestriction
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)
include hB hC

theorem ThreeSum.WeightedGlobalArenaPairRestriction.embed_injective
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) (i : ℕ) :
    Function.Injective (embed (r := r) maps τ cap Q I nB nC fB fC hB hC (i := i)) := by sorry
