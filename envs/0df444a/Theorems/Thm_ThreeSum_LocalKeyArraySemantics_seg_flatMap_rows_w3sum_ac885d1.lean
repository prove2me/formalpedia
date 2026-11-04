-- Prove2me | Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows_w3sum_ac885d1
-- name    : ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:55.484712+00:00
-- url     : https://prove2.me/theorems/d64fc479-d504-4d3d-a39a-0c2d37461fee
-- title:
--   Local Key Array Semantics: seg flat Map rows
-- statement:
--   The Local Key Array Semantics construction uses the seg flat Map rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L18-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L18-L39

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
set_option autoImplicit false
open ThreeSum ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows_w3sum_ac885d1 {α : Type*} {μ : ℕ → ℤ} (xs : List α)
    (f : α → List ℤ) (n dst : ℕ)
    (hlen : ∀ x ∈ xs, (f x).length=n)
    (hread : ∀ (j : ℕ) (hj : j < xs.length) (i : ℕ) (hi : i < n),
      μ (dst+j*n+i)=(f xs[j])[i]'(by rw [hlen _ (List.getElem_mem hj)]; exact hi)) :
    Seg μ dst (xs.flatMap f) := by sorry
