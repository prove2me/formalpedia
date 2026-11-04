-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_digit_lt
-- name    : ThreeSum.WeightEnumeration.digit_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:31.788545+00:00
-- url     : https://prove2.me/theorems/0782082f-0ea9-4054-b644-5a5dd22e3fb6
-- title:
--   Weight Enumeration: digit lt
-- statement:
--   The Weight Enumeration construction uses the digit lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L172-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L172-L173

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.digit_lt {p width k coordinate : ℕ} (hp : 0 < p) : digit p width k coordinate < p := by sorry
