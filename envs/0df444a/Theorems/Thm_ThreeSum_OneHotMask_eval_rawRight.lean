-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_rawRight
-- name    : ThreeSum.OneHotMask.eval_rawRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:55.025305+00:00
-- url     : https://prove2.me/theorems/9a1e0ec0-786b-4d74-8461-1511e7ec8ee5
-- title:
--   One Hot Mask: eval raw Right
-- statement:
--   The One Hot Mask construction uses the eval raw Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L108-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L108-L117

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.eval_rawRight {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (extend fun i => (w (i,false)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.rightWord s) := by sorry
