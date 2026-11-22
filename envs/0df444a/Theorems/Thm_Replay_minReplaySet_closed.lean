-- Prove2me | Theorems.Thm_Replay_minReplaySet_closed
-- name    : Replay.minReplaySet_closed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:08:18.10081+00:00
-- url     : https://prove2.me/theorems/72f35ec2-b76a-4abc-b16e-4fa848fb6d66
-- title:
--   Replay: min Replay Set closed
-- statement:
--   The minimum replay set is closed under predecessors.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L52-L56
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L52-L56

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

theorem Replay.minReplaySet_closed {l : Set es.Event} {x y : es.Event}
    (hy : y ≤ x) (hx : x ∈ minReplaySet es l) : y ∈ minReplaySet es l := by sorry
