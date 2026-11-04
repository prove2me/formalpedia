-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedLayout_feature_abs
-- name    : ThreeSum.TernarySignedLayout.feature_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:31.928966+00:00
-- url     : https://prove2.me/theorems/e57ddcae-4c47-4d72-8c9b-1e4f4044d1a0
-- title:
--   Ternary Signed Layout: feature abs
-- statement:
--   The Ternary Signed Layout construction uses the feature abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedLayout.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedLayout.lean#L42-L45

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction

theorem ThreeSum.TernarySignedLayout.feature_abs {J U : ℕ} {f : Coordinate J→ℤ}
    (hf : ∀ k, |f k|≤(U : ℤ)) (i : ℕ) : |feature f i|≤(U : ℤ) := by sorry
