-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_extend_fin
-- name    : ThreeSum.OneHotMask.extend_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:35.870639+00:00
-- url     : https://prove2.me/theorems/1a097f07-4880-402c-900c-16d0a15b2d19
-- title:
--   One Hot Mask: extend fin
-- statement:
--   The One Hot Mask construction uses the extend fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L76-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L76-L77

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by sorry
