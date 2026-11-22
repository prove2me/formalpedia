-- Prove2me | Theorems.Thm_Replay_minReplaySet_compatible_with_log
-- name    : Replay.minReplaySet_compatible_with_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:08:32.596714+00:00
-- url     : https://prove2.me/theorems/dff0d998-1470-4486-987a-d85a3f8531b2
-- title:
--   Replay: min Replay Set compatible with log
-- statement:
--   The minimum replay set is compatible with the log.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L76-L82
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L76-L82

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

theorem Replay.minReplaySet_compatible_with_log {l : Set es.Event}
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ x ∈ minReplaySet es l, ∀ e ∈ l, ¬(x # e) := by sorry
