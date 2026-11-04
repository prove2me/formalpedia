-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_coordinateIndex_lt
-- name    : ThreeSum.WeightEnumeration.coordinateIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:32.314337+00:00
-- url     : https://prove2.me/theorems/718d0a88-fbb2-4287-8a83-9c87c8bfb5ed
-- title:
--   Weight Enumeration: coordinate Index lt
-- statement:
--   The Weight Enumeration construction uses the coordinate Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L142-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L142-L145

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.coordinateIndex_lt {L : ℕ} (i : Fin L × Bool) : coordinateIndex i < 2*L := by sorry
