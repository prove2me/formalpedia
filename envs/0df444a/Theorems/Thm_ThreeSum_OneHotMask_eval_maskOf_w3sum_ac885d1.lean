-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf_w3sum_ac885d1
-- name    : ThreeSum.OneHotMask.eval_maskOf_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:07.626699+00:00
-- url     : https://prove2.me/theorems/658ccc1d-a3ae-410a-ab2b-ba9023feb841
-- title:
--   One Hot Mask: eval mask Of
-- statement:
--   The One Hot Mask construction uses the eval mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L50-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L50-L71

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.eval_maskOf_w3sum_ac885d1 {L : ℕ} (s : Finset ℕ) (hs : s ⊆ range L)
    (w0 w1 : ℕ → ℕ) :
    eval w0 w1 L (maskOf s) = ∑ i ∈ range L, if i ∈ s then w1 i else w0 i := by sorry
