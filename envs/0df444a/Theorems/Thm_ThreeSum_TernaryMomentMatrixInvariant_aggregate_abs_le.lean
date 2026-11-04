-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_aggregate_abs_le
-- name    : ThreeSum.TernaryMomentMatrixInvariant.aggregate_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:07.156122+00:00
-- url     : https://prove2.me/theorems/b81dbcf6-efdd-4114-ae0a-3f587d26251f
-- title:
--   Ternary Moment Matrix Invariant: aggregate abs le
-- statement:
--   The Ternary Moment Matrix Invariant construction uses the aggregate abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L58-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L58-L70

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule

theorem ThreeSum.TernaryMomentMatrixInvariant.aggregate_abs_le (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ)
    (k i V : ℕ) (hscore : ∀ c∈done, |score c.1 c.2 i|≤(V : ℤ)) :
    |aggregate done score k i|≤(done.length : ℤ)*V := by sorry
