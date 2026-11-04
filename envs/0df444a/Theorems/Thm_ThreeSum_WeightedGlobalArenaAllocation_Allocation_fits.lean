-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_fits
-- name    : ThreeSum.WeightedGlobalArenaAllocation.Allocation.fits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:04:24.973243+00:00
-- url     : https://prove2.me/theorems/72de69b8-32c1-4e1c-9084-b473db7d8ddd
-- title:
--   Allocation: fits
-- statement:
--   The Allocation construction uses the fits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L42-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L42-L52

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocation.Allocation.fits {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    Fits (capacity A.D A.E (n+U)) (numbers maps τ cap M b K H drift scale n U j) := by sorry
