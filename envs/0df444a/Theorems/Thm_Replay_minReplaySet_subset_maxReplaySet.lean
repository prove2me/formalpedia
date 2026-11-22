-- Prove2me | Theorems.Thm_Replay_minReplaySet_subset_maxReplaySet
-- name    : Replay.minReplaySet_subset_maxReplaySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:08:17.329234+00:00
-- url     : https://prove2.me/theorems/936ed190-8cde-4ee5-8e1f-a66de6f78360
-- title:
--   Replay: min Replay Set subset max Replay Set
-- statement:
--   The maximum replay set contains the minimum replay set.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L59-L61
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L59-L61

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

theorem Replay.minReplaySet_subset_maxReplaySet {l : Set es.Event} :
    minReplaySet es l ⊆ maxReplaySet es l := by sorry
