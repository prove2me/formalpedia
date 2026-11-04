-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_sound
-- name    : ThreeSum.WeightedGlobalNativePairAccess.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:23:01.6636+00:00
-- url     : https://prove2.me/theorems/666cd243-bd17-47a6-adeb-db58861f71e5
-- title:
--   Weighted Global Native Pair Access: sound
-- statement:
--   The physical pair type always refers to valid original source positions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairAccess.lean#L28-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairAccess.lean#L28-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalNativePairAccess.sound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (A B C : ℕ→ℤ) (position : ℕ→ℕ) (nA : ℕ)
    (hpos : ∀ i<S.front.count, position i<nA) :
    (∃ i<S.front.count, ∃ p : Pair S i, mode B C p=A (position i)) →
    ∃ i<nA, ∃ j<S.left.NL, ∃ k<S.right.NL, C k=A i+B j := by sorry
