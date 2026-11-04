-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_field_sizes
-- name    : ThreeSum.WeightedGlobalArenaPhaseBudget.field_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:04:53.498946+00:00
-- url     : https://prove2.me/theorems/e95a66ad-0e3c-4511-9bae-854b0f3493ef
-- title:
--   Weighted Global Arena Phase Budget: field sizes
-- statement:
--   Exact scalar field-size guards for the extension degree computed by the
--   actual prelude.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L36-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L36-L51

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPhaseBudget.field_sizes (J K : ℕ) (hK : 0<K)
    (hcard : Fintype.card E=p^(menuDegree p (J+2) K)) :
    8*(J+2)*p^2≤Fintype.card E ∧ 8*(J+2)*p^(2*(K+K))≤Fintype.card E := by sorry
