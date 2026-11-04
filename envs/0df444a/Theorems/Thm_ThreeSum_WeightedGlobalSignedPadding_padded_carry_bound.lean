-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_padded_carry_bound
-- name    : ThreeSum.WeightedGlobalSignedPadding.padded_carry_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:14:36.457813+00:00
-- url     : https://prove2.me/theorems/b06a427c-e08d-4151-9aef-ae1733836f76
-- title:
--   Weighted Global Signed Padding: padded carry bound
-- statement:
--   The Weighted Global Signed Padding construction uses the padded carry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPadding.lean#L66-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPadding.lean#L66-L115

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

theorem ThreeSum.WeightedGlobalSignedPadding.padded_carry_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) :
    (2 : ℝ)^paddedLength b U (radixLength m n) ≤
      carryConstant b*(n : ℝ)^carryExponent m b κ := by sorry
