-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_value_eq_model
-- name    : ThreeSum.WeightedGlobalArenaPrefixPotential.value_eq_model
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:21:49.180176+00:00
-- url     : https://prove2.me/theorems/3cd1424a-a50c-4173-a145-0517437db44e
-- title:
--   Weighted Global Arena Prefix Potential: value eq model
-- statement:
--   Literal physical positions, local dictionary tuple indices, actual wanted
--   ordinals and every K-tuple are in bijection with the retained prefix model.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L46-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L46-L51

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

theorem ThreeSum.WeightedGlobalArenaPrefixPotential.value_eq_model (r K : ℕ) : value maps τ cap I L R row root Q r K=
    potential ((M maps τ cap I L R row root).matrix (r := r) (K := K)) := by sorry
