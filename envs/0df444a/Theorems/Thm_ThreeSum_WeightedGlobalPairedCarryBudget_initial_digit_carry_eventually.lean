-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCarryBudget_initial_digit_carry_eventually
-- name    : ThreeSum.WeightedGlobalPairedCarryBudget.initial_digit_carry_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:33:36.139029+00:00
-- url     : https://prove2.me/theorems/32881ff7-c2b4-4288-8380-36cac3a0b9d7
-- title:
--   Weighted Global Paired Carry Budget: initial digit carry eventually
-- statement:
--   The Weighted Global Paired Carry Budget construction uses the initial digit carry eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCarryBudget.lean#L16-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCarryBudget.lean#L16-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCarryBudget
open Filter Real WeightedGlobalSignedPreparationBudget WeightedGlobalSignedPadding WeightedGlobalCoverScale
open scoped Topology

theorem ThreeSum.WeightedGlobalPairedCarryBudget.initial_digit_carry_eventually {m b K : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m b κ<δ) (hδ : 4*δ<1)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      (2^(paddedLength b (U n) (radixLength m n)))^4*
        (paddedLength b (U n) (radixLength m n)+2)^(8*K)≤n := by sorry
