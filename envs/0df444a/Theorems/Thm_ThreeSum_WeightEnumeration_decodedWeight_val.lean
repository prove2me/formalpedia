-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_decodedWeight_val
-- name    : ThreeSum.WeightEnumeration.decodedWeight_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:33.995382+00:00
-- url     : https://prove2.me/theorems/fab55b3d-cc00-45cf-8c3d-8bf3c153b524
-- title:
--   Weight Enumeration: decoded Weight val
-- statement:
--   The Weight Enumeration construction uses the decoded Weight val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L175-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L175-L177

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (decodedWeight (K := ZMod p) L p k i).val = digit p (2*L) k (coordinateIndex i) := by sorry
