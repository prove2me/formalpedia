-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_matrix_equiv
-- name    : ThreeSum.WeightedGlobalArenaPrefixPotential.matrix_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:22:31.743267+00:00
-- url     : https://prove2.me/theorems/8b9d9e08-3840-4670-9532-2c9ef1fb7b91
-- title:
--   Weighted Global Arena Prefix Potential: matrix equiv
-- statement:
--   The Weighted Global Arena Prefix Potential construction uses the matrix equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L38-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L38-L40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPairs
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPotential
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)

theorem ThreeSum.WeightedGlobalArenaPrefixPotential.matrix_equiv {r K : ℕ} (x : Index maps τ cap I L R row root Q r K) :
    (M maps τ cap I L R row root).matrix (equiv maps τ cap I L R row root Q r K x)=
      matrix maps τ cap I L R row root Q x := by sorry
