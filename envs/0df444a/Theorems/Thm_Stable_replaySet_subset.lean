-- Prove2me | Theorems.Thm_Stable_replaySet_subset
-- name    : Stable.replaySet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:06:17.105201+00:00
-- url     : https://prove2.me/theorems/e6627128-094a-49a9-9fa1-3ebb3cfd99a9
-- title:
--   Stable: replay Set subset
-- statement:
--   The Stable construction uses the replay Set subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L26-L29
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L26-L29

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
include hc hlc

theorem Stable.replaySet_subset : replaySet F c l ⊆ c := by sorry
