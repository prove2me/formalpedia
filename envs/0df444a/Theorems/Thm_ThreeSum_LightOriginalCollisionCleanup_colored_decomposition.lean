-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_colored_decomposition
-- name    : ThreeSum.LightOriginalCollisionCleanup.colored_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:12.279102+00:00
-- url     : https://prove2.me/theorems/e5585258-eae8-49c2-a6cf-edc27cb8295d
-- title:
--   Light Original Collision Cleanup: colored decomposition
-- statement:
--   Every original colored solution is either found during literal collision
--   cleanup or survives in both source classes. This accounts for all inputs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L205-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L205-L232

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalCollisionCleanup.colored_decomposition (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i<nA, ∃ j<nB, ∃ k<nC, C k=A i+B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i<nA, ∃ j∈good keysB (counts keysB nB) nB, ∃ k∈good keysC (counts keysC nC) nC,
        C k=A i+B j := by sorry
