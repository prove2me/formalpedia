-- Prove2me | Theorems.Thm_Replay_minReplaySet_contains_log
-- name    : Replay.minReplaySet_contains_log
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:43.758152+00:00
-- url     : https://prove2.me/theorems/615f445c-76b5-4c7a-8136-91db4edbb038
-- title:
--   Replay: min Replay Set contains log
-- statement:
--   The minimum replay set contains the log.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L46-L49
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L46-L49

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

theorem Replay.minReplaySet_contains_log {l : Set es.Event} : l ⊆ minReplaySet es l := by sorry
