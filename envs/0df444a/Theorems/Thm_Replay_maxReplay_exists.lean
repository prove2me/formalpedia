-- Prove2me | Theorems.Thm_Replay_maxReplay_exists
-- name    : Replay.maxReplay_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:08:33.554807+00:00
-- url     : https://prove2.me/theorems/ffd43433-174b-41e3-a82d-84400896c3ca
-- title:
--   Replay: max Replay exists
-- statement:
--   A greatest replay exists once some compatible computation reaches
--   `maxReplaySet`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L138-L143
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L138-L143

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

theorem Replay.maxReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es.toFamily,
      (Replay.conf es.toFamily σ).1 = maxReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMaxReplay es.toFamily es.conflict l σ := by sorry
