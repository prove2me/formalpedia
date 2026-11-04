-- Prove2me | Theorems.Thm_ThreeSum_OutputKeyMasks_eval_difference
-- name    : ThreeSum.OutputKeyMasks.eval_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:51.760897+00:00
-- url     : https://prove2.me/theorems/b2d0afdc-2b83-4cb4-96d6-9dae180d5617
-- title:
--   Output Key Masks: eval difference
-- statement:
--   The Output Key Masks construction uses the eval difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L28-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L28-L37

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
set_option autoImplicit false
open ThreeSum ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators

theorem ThreeSum.OutputKeyMasks.eval_difference {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (fun _ => 0) L (subsetMask Q) : ℤ)-
      (eval (extend fun i => (w (i,false)).val) (fun _ => 0) L (subsetMask Q) : ℤ)
      = rawOutput w Q := by sorry
