-- Prove2me | Theorems.Thm_Replay_minReplaySet_is_minimal_replay
-- name    : Replay.minReplaySet_is_minimal_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:53.610794+00:00
-- url     : https://prove2.me/theorems/0c4f9f33-ffb0-4520-a7fe-94c47437850d
-- title:
--   Replay: min Replay Set is minimal replay
-- statement:
--   A computation reaching `minReplaySet` is a minimal replay.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L85-L98
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L85-L98

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

theorem Replay.minReplaySet_is_minimal_replay {l : Set es.Event} {σ : Computations es.toFamily}
    (h_conf : (Replay.conf es.toFamily σ).1 = minReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMinReplay es.toFamily es.conflict l σ := by sorry
