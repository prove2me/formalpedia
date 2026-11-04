-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_constants
-- name    : ThreeSum.WeightedGlobalArenaAllocation.Allocation.constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:03:58.948474+00:00
-- url     : https://prove2.me/theorems/d1ef99ef-3209-4699-bbec-fc7c233978a6
-- title:
--   Allocation: constants
-- statement:
--   The Allocation construction uses the constants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L69-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L69-L79

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocation.Allocation.constants {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U : ℕ) :
    A.D≤capacity A.D A.E (n+U) ∧ A.E≤capacity A.D A.E (n+U) ∧
      n+U+1≤capacity A.D A.E (n+U) := by sorry
