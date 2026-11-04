-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_Normalized_bounded
-- name    : ThreeSum.LightTernaryColorPrelude.Normalized.bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:30.535472+00:00
-- url     : https://prove2.me/theorems/12b6780a-48f5-472d-9bb0-1dddb954c6e4
-- title:
--   Normalized: bounded
-- statement:
--   The Normalized construction uses the bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L279-L281
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L279-L281

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryColorPrelude.Normalized.bounded {μ : ℕ→ℤ} {base n U : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) (hb : ∀ z∈original, |z|≤(U:ℤ)) :
    ∀ z∈L, |z|≤(U:ℤ) := by sorry
