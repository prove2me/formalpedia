-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_le_w3sum_ac885d1
-- name    : ThreeSum.OneHotMask.eval_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:24.383881+00:00
-- url     : https://prove2.me/theorems/d49df6a5-ffbb-48ef-99ec-213c94538fbe
-- title:
--   One Hot Mask: eval le
-- statement:
--   The One Hot Mask construction uses the eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L26-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L26-L41

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.eval_le_w3sum_ac885d1 {L m U : ℕ} {w0 w1 : ℕ → ℕ}
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) :
    eval w0 w1 L m ≤ L*U := by sorry
