-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_partitionCap_le_poly_mul_group
-- name    : ThreeSum.TernaryCoverPartitionLower.partitionCap_le_poly_mul_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:45.602294+00:00
-- url     : https://prove2.me/theorems/c485f157-5e1a-4c64-86bf-c383356e7b6f
-- title:
--   Ternary Cover Partition Lower: partition Cap le poly mul group
-- statement:
--   The Ternary Cover Partition Lower construction uses the partition Cap le poly mul group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L38-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPartitionLower.lean#L38-L43

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds

theorem ThreeSum.TernaryCoverPartitionLower.partitionCap_le_poly_mul_group (r s : ℕ) :
    2 ^ (2*r) * 3 ^ (3*s) ≤
      (2*r+1)*(3*s+1)*(2*s+1)*
        ((2*r).choose r * (3*s).choose s * (2*s).choose s) := by sorry
