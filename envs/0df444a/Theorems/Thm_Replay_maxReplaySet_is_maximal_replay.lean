-- Prove2me | Theorems.Thm_Replay_maxReplaySet_is_maximal_replay
-- name    : Replay.maxReplaySet_is_maximal_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:55.0635+00:00
-- url     : https://prove2.me/theorems/fcf8fd70-e922-4e38-b473-48829e6c14c2
-- title:
--   Replay: max Replay Set is maximal replay
-- statement:
--   A computation reaching `maxReplaySet` is a maximal replay.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L101-L126
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L101-L126

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

theorem Replay.maxReplaySet_is_maximal_replay {l : Set es.Event} {σ : Computations es.toFamily}
    (h_conf : (Replay.conf es.toFamily σ).1 = maxReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMaxReplay es.toFamily es.conflict l σ := by sorry
