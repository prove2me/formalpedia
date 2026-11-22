-- Prove2me | Theorems.Thm_Replay_downset_closed
-- name    : Replay.downset_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:19.442421+00:00
-- url     : https://prove2.me/theorems/ffa90375-f412-46b3-8c6b-cd8a30ddcf9f
-- title:
--   Replay: downset closed
-- statement:
--   The downset is closed under taking predecessors.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L41-L43
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L41-L43

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

theorem Replay.downset_closed {e x y : es.Event} (hxy : x ≤ y) (hy : y ∈ downset es e) :
    x ∈ downset es e := by sorry
