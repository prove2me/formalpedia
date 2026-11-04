-- Prove2me | Theorems.Thm_ThreeSum_LightColoredTwoSum_hit_succ
-- name    : ThreeSum.LightColoredTwoSum.hit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:15.005455+00:00
-- url     : https://prove2.me/theorems/582e313d-69f0-4ac7-8895-a3da4f01375d
-- title:
--   Light Colored Two Sum: hit succ
-- statement:
--   The Light Colored Two Sum construction uses the hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L43-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L43-L53

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem ThreeSum.LightColoredTwoSum.hit_succ (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) :
    Hit scan target m (j+1) bad sign ↔ Hit scan target m j bad sign ∨ ∃ k<m, target k=sign*scan j+bad := by sorry
