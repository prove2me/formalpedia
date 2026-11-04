-- Prove2me | Theorems.Thm_ThreeSum_OriginalThreeSum_distinct_iff_end
-- name    : ThreeSum.OriginalThreeSum.distinct_iff_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:57.007692+00:00
-- url     : https://prove2.me/theorems/a22f80d0-d3bc-4875-9d79-e1fb2a1a7276
-- title:
--   Original Three Sum: distinct iff end
-- statement:
--   The Original Three Sum construction uses the distinct iff end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L10-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L10-L16

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec

theorem ThreeSum.OriginalThreeSum.distinct_iff_end {n : ℕ} (x : Fin n → ℤ) :
    Coloring.DistinctZeroSum x ↔ EndStatement.ThreeSum.yes x := by sorry
