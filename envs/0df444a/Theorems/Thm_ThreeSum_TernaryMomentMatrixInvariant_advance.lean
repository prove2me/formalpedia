-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_advance
-- name    : ThreeSum.TernaryMomentMatrixInvariant.advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:01.486446+00:00
-- url     : https://prove2.me/theorems/bad561d5-9ac9-4cd9-bcc6-1952a969c213
-- title:
--   Ternary Moment Matrix Invariant: advance
-- statement:
--   The Ternary Moment Matrix Invariant construction uses the advance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L23-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean#L23-L56

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule

theorem ThreeSum.TernaryMomentMatrixInvariant.advance {reference μ ν : ℕ→ℤ} {matrix count terms boundary k j : ℕ}
    (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ)
    (hk : k<terms) (hwindow : matrix+terms*count≤boundary)
    (hI : Holds reference matrix count terms boundary done score μ)
    (hrow : ∀ i<count, ν (matrix+k*count+i)=aggregate done score k i+score k j i)
    (hkeep : ∀ a<boundary, (a<matrix+k*count ∨ matrix+k*count+count≤a) → ν a=μ a) :
    Holds reference matrix count terms boundary (done++[(k,j)]) score ν := by sorry
