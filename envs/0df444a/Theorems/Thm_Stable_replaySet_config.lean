-- Prove2me | Theorems.Thm_Stable_replaySet_config
-- name    : Stable.replaySet_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:06:22.62742+00:00
-- url     : https://prove2.me/theorems/6d501682-5e32-4e99-bd84-785429cac969
-- title:
--   Stable: replay Set config
-- statement:
--   It is a configuration: each history is one by stability, their union by coherence.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L33-L38
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L33-L38

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
include hc hlc

theorem Stable.replaySet_config (hS : Stable F) (hC : Coherent F) : F.Config (replaySet F c l) := by sorry
