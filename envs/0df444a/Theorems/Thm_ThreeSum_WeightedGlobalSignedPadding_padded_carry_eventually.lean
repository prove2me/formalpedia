-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_padded_carry_eventually
-- name    : ThreeSum.WeightedGlobalSignedPadding.padded_carry_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:11:02.014714+00:00
-- url     : https://prove2.me/theorems/16cf7be2-5b7a-4e98-a034-0a4333db568f
-- title:
--   Weighted Global Signed Padding: padded carry eventually
-- statement:
--   The Weighted Global Signed Padding construction uses the padded carry eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPadding.lean#L126-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPadding.lean#L126-L135

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology

theorem ThreeSum.WeightedGlobalSignedPadding.padded_carry_eventually {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : carryExponent m b κ<ε)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ)^paddedLength b (U n) (radixLength m n) ≤ (n : ℝ)^ε := by sorry
