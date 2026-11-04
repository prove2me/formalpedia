-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_subsetMask
-- name    : ThreeSum.OneHotMask.eval_subsetMask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:18.799998+00:00
-- url     : https://prove2.me/theorems/a2c21d4d-ae31-471a-92fc-fb221b80b54b
-- title:
--   One Hot Mask: eval subset Mask
-- statement:
--   The One Hot Mask construction uses the eval subset Mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L89-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L89-L95

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by sorry
