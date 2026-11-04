-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_pos_iff
-- name    : ThreeSum.LightTernaryRowSelector.pick_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:53.485861+00:00
-- url     : https://prove2.me/theorems/f7e111c4-53d1-4ef7-8a40-6ebc36c15ab1
-- title:
--   Light Ternary Row Selector: pick pos iff
-- statement:
--   The Light Ternary Row Selector construction uses the pick pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRowSelector.lean#L27-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRowSelector.lean#L27-L44

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRowSelector
open Light

theorem ThreeSum.LightTernaryRowSelector.pick_pos_iff (good : ℕ → Prop) [DecidablePred good] (n : ℕ) :
    0 < pick good n ↔ ∃ i < n, good i := by sorry
