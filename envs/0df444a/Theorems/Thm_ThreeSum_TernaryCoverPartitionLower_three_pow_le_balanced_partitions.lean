-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_three_pow_le_balanced_partitions
-- name    : ThreeSum.TernaryCoverPartitionLower.three_pow_le_balanced_partitions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:05.94189+00:00
-- url     : https://prove2.me/theorems/af330799-a63a-4911-8f2b-fa1cc9655eda
-- title:
--   Ternary Cover Partition Lower: three pow le balanced partitions
-- statement:
--   The Ternary Cover Partition Lower construction uses the three pow le balanced partitions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L28-L36

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds

theorem ThreeSum.TernaryCoverPartitionLower.three_pow_le_balanced_partitions (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1)*(2*s+1)*((3*s).choose s*(2*s).choose s) := by sorry
