-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_idxOf_map_injective
-- name    : ThreeSum.WeightEnumeration.idxOf_map_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:31.663831+00:00
-- url     : https://prove2.me/theorems/22d61a58-abce-44d0-afb2-5062f1f67037
-- title:
--   Weight Enumeration: idx Of map injective
-- statement:
--   The Weight Enumeration construction uses the idx Of map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L106-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L106-L111

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.idxOf_map_injective {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (l : List ι) (x : ι) :
    (l.map f).idxOf (f x) = l.idxOf x := by sorry
