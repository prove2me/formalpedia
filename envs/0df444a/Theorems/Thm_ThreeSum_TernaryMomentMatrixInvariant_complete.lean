-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_complete
-- name    : ThreeSum.TernaryMomentMatrixInvariant.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:54.211379+00:00
-- url     : https://prove2.me/theorems/5878d9b3-7035-4c64-81c1-9b726428f3a1
-- title:
--   Ternary Moment Matrix Invariant: complete
-- statement:
--   The Ternary Moment Matrix Invariant construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L72-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L72-L78

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule

theorem ThreeSum.TernaryMomentMatrixInvariant.complete {reference μ : ℕ→ℤ} {matrix count terms boundary : ℕ}
    (score : ℕ→ℕ→ℕ→ℤ)
    (hI : Holds reference matrix count terms boundary (channels terms) score μ) :
    ∀ k<terms, ∀ i<count,
      μ (matrix+k*count+i)=∑ j∈Finset.range (k+1), score k j i := by sorry
