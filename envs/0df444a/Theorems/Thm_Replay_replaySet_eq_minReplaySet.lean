-- Prove2me | Theorems.Thm_Replay_replaySet_eq_minReplaySet
-- name    : Replay.replaySet_eq_minReplaySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:08:43.889429+00:00
-- url     : https://prove2.me/theorems/0a9cf07a-dc2f-49af-8b98-f6483f31d2a3
-- title:
--   Replay: replay Set eq min Replay Set
-- statement:
--   Hence the general least replay set agrees with the prime one.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L159-L161
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L159-L161

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
open Log
local infixl:50 " ⊨ " => PES.compatibleWithLog es
open Replay
local infixl:50 " ## " => es.minimalConflict
local infixl:50 " # " => es.conflict

theorem Replay.replaySet_eq_minReplaySet {c l : Set es.Event} (hc : isConf es c) (hlc : l ⊆ c) :
    Stable.replaySet es.toFamily c l = minReplaySet es l := by sorry
