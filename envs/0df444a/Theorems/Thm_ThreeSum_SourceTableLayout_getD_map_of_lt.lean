-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_getD_map_of_lt
-- name    : ThreeSum.SourceTableLayout.getD_map_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:27.035796+00:00
-- url     : https://prove2.me/theorems/4cad615a-71a2-4b9a-8c12-14f2559ce7e2
-- title:
--   Source Table Layout: get D map of lt
-- statement:
--   The Source Table Layout construction uses the get D map of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_List_getD_map_of_lt

set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.getD_map_of_lt {α β : Type*} (l : List α) (f : α → β)
    (a : α) (b : β) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i b = f (l.getD i a) := by sorry
