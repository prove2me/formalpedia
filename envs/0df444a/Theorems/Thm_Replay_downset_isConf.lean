-- Prove2me | Theorems.Thm_Replay_downset_isConf
-- name    : Replay.downset_isConf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:47.919813+00:00
-- url     : https://prove2.me/theorems/03b598e6-2a1f-461f-aa16-4ffa449d5d04
-- title:
--   Replay: downset is Conf
-- statement:
--   The downset is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L146-L149
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L146-L149

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

theorem Replay.downset_isConf (e : es.Event) : isConf es (downset es e) := by sorry
