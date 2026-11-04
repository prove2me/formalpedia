-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_three_pow_le_weighted_choose
-- name    : ThreeSum.TernaryCoverPartitionLower.three_pow_le_weighted_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:05.532678+00:00
-- url     : https://prove2.me/theorems/97cb263c-2308-4292-aaed-972b33a0fcb1
-- title:
--   Ternary Cover Partition Lower: three pow le weighted choose
-- statement:
--   The Ternary Cover Partition Lower construction uses the three pow le weighted choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L10-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L10-L26

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds

theorem ThreeSum.TernaryCoverPartitionLower.three_pow_le_weighted_choose (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1) * (3*s).choose s * 2 ^ (2*s) := by sorry
