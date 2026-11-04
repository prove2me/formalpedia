-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectorAllocation_controls
-- name    : ThreeSum.WeightedGlobalArenaSelectorAllocation.controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:29:12.309196+00:00
-- url     : https://prove2.me/theorems/31f67afc-3675-4075-9c06-dfca7029e2d0
-- title:
--   Weighted Global Arena Selector Allocation: controls
-- statement:
--   The Weighted Global Arena Selector Allocation construction uses the controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L51-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L51-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_controls

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSelectorAllocation.controls (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j nO : ℕ)
    (hO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    let T := total maps τ cap M b K H drift scale n U j
    1≤T ∧ p^j≤T ∧ (p^(2*K))^j≤T ∧ 9^j*n^2≤T ∧
    (drift*scale)^j*LightTernaryInitialBudgets.initial K b n
      (LightWeightedGlobalDimensions.J M b n U) nO≤T ∧
    (numbers maps τ cap M b K H drift scale n U j).candidateScore≤T ∧
    (p^(LightWeightedGlobalDimensions.dim M b p K n U))^2≤T := by sorry
