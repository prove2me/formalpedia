-- Prove2me | Theorems.Thm_ThreeSum_BandPartition_size_mul_le
-- name    : ThreeSum.BandPartition.size_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:06.401299+00:00
-- url     : https://prove2.me/theorems/ed75a068-249a-4b9f-8c84-de7ea2006c70
-- title:
--   Band Partition: size mul le
-- statement:
--   A finite ceiling bound, including the empty input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L33-L38

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition

theorem ThreeSum.BandPartition.size_mul_le (n g : ℕ) : size n g*g ≤ n+g := by sorry
