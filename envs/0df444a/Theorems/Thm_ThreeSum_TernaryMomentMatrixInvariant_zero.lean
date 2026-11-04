-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_zero
-- name    : ThreeSum.TernaryMomentMatrixInvariant.zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:46.298745+00:00
-- url     : https://prove2.me/theorems/313176ca-fe23-4283-b65f-c73a46d42877
-- title:
--   Ternary Moment Matrix Invariant: zero
-- statement:
--   The Ternary Moment Matrix Invariant construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L13-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L13-L21

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule

theorem ThreeSum.TernaryMomentMatrixInvariant.zero {reference μ : ℕ→ℤ} {matrix count terms boundary : ℕ}
    (score : ℕ→ℕ→ℕ→ℤ)
    (hzero : ∀ k<terms, ∀ i<count, μ (matrix+k*count+i)=0)
    (hkeep : SameOutside reference μ matrix (terms*count)) :
    Holds reference matrix count terms boundary [] score μ := by sorry
