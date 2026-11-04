-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_field_sizes
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.field_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:11:26.892513+00:00
-- url     : https://prove2.me/theorems/b2111b0d-711d-4b5e-8cc3-78ba68e20a76
-- title:
--   Weighted Global Colored Loop Setup: field sizes
-- statement:
--   The Weighted Global Colored Loop Setup construction uses the field sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L114-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L114-L118

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_field_sizes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredLoopSetup.field_sizes :
    8*(J P n+2)*P.p^2≤Fintype.card (Extension P n c) ∧
    8*(J P n+2)*P.p^(2*(P.K+P.K))≤Fintype.card (Extension P n c) := by sorry
