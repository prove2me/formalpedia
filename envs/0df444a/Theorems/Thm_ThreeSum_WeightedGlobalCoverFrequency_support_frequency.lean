-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_support_frequency
-- name    : ThreeSum.WeightedGlobalCoverFrequency.support_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:47.76371+00:00
-- url     : https://prove2.me/theorems/63243011-e758-4857-9dc8-f15c4ca4d147
-- title:
--   Weighted Global Cover Frequency: support frequency
-- statement:
--   The Weighted Global Cover Frequency construction uses the support frequency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L21-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L21-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators

theorem ThreeSum.WeightedGlobalCoverFrequency.support_frequency {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℕ) (N p C a : ℕ) (hN : 0 < N)
    (hfirst : N * Fintype.card Ω ≤ 2*p^2*∑ w, f w)
    (hsecond : (∑ w, f w^2) ≤ C*Fintype.card Ω)
    (hscale : 4*p^4*C ≤ a*N^2) :
    Fintype.card Ω ≤ a * (univ.filter fun w => f w ≠ 0).card := by sorry
