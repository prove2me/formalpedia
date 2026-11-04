-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_support_frequency
-- name    : ThreeSum.TernaryCoverFrequency.support_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:39.682043+00:00
-- url     : https://prove2.me/theorems/49ff56cd-fa52-4d5e-baae-80021967ef25
-- title:
--   Ternary Cover Frequency: support frequency
-- statement:
--   The Ternary Cover Frequency construction uses the support frequency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L14-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L14-L55

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators

theorem ThreeSum.TernaryCoverFrequency.support_frequency {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℕ) (N p C a : ℕ) (hN : 0 < N)
    (hfirst : N * Fintype.card Ω ≤ 2*p^2*∑ w, f w)
    (hsecond : (∑ w, f w^2) ≤ C*Fintype.card Ω)
    (hscale : 4*p^4*C ≤ a*N^2) :
    Fintype.card Ω ≤ a * (univ.filter fun w => f w ≠ 0).card := by sorry
