-- Prove2me | Theorems.Thm_Replay_minReplay_exists
-- name    : Replay.minReplay_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:08:29.675332+00:00
-- url     : https://prove2.me/theorems/89473f7a-f488-4b84-a638-be9174bb403c
-- title:
--   Replay: min Replay exists
-- statement:
--   The least replay exists when some compatible computation reaches `minReplaySet`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L129-L134
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L129-L134

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

theorem Replay.minReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es.toFamily,
      (Replay.conf es.toFamily σ).1 = minReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMinReplay es.toFamily es.conflict l σ := by sorry
