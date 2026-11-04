-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixStep_sum_appended_bound
-- name    : ThreeSum.WeightedGlobalArenaPrefixStep.sum_appended_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:33:53.895639+00:00
-- url     : https://prove2.me/theorems/81d7cc48-1073-43eb-b65d-846f5d1a5e4c
-- title:
--   Weighted Global Arena Prefix Step: sum appended bound
-- statement:
--   Original physical paired potentials satisfy the proved menu average,
--   including dictionary trimming, all carry/requester occurrences and all groups.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L114-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L114-L137

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPrefixStep.sum_appended_bound (ℓ : E→ₗ[ZMod p] ZMod p) (hℓ : ℓ≠0)
    (V : Submodule (ZMod p) (Fin Λ→ZMod p)) (hV : V≠⊤) (hp : 3≤p)
    (newroot : E×E→ℕ→ZMod p) (r K b : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*Λ*p^2≤Fintype.card E) (hsize : 8*Λ*p^(2*(K+K))≤Fintype.card E) :
    p^(K+K)*(∑ seed∈admissible Λ ℓ V,
      value maps τ cap I L R (Function.update row r (TernaryOriginalRowMenu.row Λ ℓ seed))
        (fun o => Function.update (root o) r (newroot seed o)) Q (r+1) K)≤
      3*(admissible Λ ℓ V).card*F*(vertices (fixedLength m) (fixedPi m)).card*
        (2^(fixedPi m 1)*3^(fixedPi m 2))^K*value maps τ cap I L R row root Q r K := by sorry
