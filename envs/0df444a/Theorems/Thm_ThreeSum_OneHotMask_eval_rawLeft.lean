-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_rawLeft
-- name    : ThreeSum.OneHotMask.eval_rawLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:58.455126+00:00
-- url     : https://prove2.me/theorems/5f5a532c-dccd-403c-9d5f-eb4a2f57e097
-- title:
--   One Hot Mask: eval raw Left
-- statement:
--   The One Hot Mask construction uses the eval raw Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L97-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L97-L106

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.eval_rawLeft {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,false)).val) (extend fun i => (w (i,true)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.leftWord s) := by sorry
