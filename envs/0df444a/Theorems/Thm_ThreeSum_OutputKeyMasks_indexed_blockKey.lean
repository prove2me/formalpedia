-- Prove2me | Theorems.Thm_ThreeSum_OutputKeyMasks_indexed_blockKey
-- name    : ThreeSum.OutputKeyMasks.indexed_blockKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:57.583279+00:00
-- url     : https://prove2.me/theorems/6be0b609-09c5-4b15-874f-5ae9a35b0bf4
-- title:
--   Output Key Masks: indexed block Key
-- statement:
--   The Output Key Masks construction uses the indexed block Key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L44-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L44-L52

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
set_option autoImplicit false
open ThreeSum ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators

theorem ThreeSum.OutputKeyMasks.indexed_blockKey {h : ℕ} (o : Occurrence h)
    (i : Fin ((512*h).choose (2*h))) :
    (eval (BlockCoefficientRows.mapRow h true o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ)-
      (eval (BlockCoefficientRows.mapRow h false o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ) =
      blockKey (o,GlobalKeyEnumeration.layerRecord h i) := by sorry
