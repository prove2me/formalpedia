-- Prove2me | Theorems.Thm_ThreeSum_LightColoredTwoSum_lookup_positive_iff
-- name    : ThreeSum.LightColoredTwoSum.lookup_positive_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:57.15019+00:00
-- url     : https://prove2.me/theorems/6b5994b4-9540-42f1-8317-9e351ecdda9e
-- title:
--   Light Colored Two Sum: lookup positive iff
-- statement:
--   The Light Colored Two Sum construction uses the lookup positive iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L12-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L12-L29

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem ThreeSum.LightColoredTwoSum.lookup_positive_iff (target : ℕ → ℤ) (m : ℕ) (x : ℤ)
    (hs : ∀ i j, i<j → j<m → target i<target j) :
    0<LightBandLookup.result target target m x ↔ ∃ j<m, target j=x := by sorry
