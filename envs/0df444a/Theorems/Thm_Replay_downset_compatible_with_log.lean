-- Prove2me | Theorems.Thm_Replay_downset_compatible_with_log
-- name    : Replay.downset_compatible_with_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:49.588823+00:00
-- url     : https://prove2.me/theorems/5322fd06-9ed2-435d-823a-ceee127c62f0
-- title:
--   Replay: downset compatible with log
-- statement:
--   Below an event of a conflict-free log, every event is compatible with the
--   log.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L65-L73
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L65-L73

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

theorem Replay.downset_compatible_with_log {l : Set es.Event} {e x : es.Event}
    (he : e ∈ l) (hxe : x ≤ e)
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ e' ∈ l, ¬(x # e') := by sorry
