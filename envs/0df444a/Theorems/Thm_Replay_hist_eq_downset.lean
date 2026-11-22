-- Prove2me | Theorems.Thm_Replay_hist_eq_downset
-- name    : Replay.hist_eq_downset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:56.983386+00:00
-- url     : https://prove2.me/theorems/d3d71d0a-7fd5-468a-aace-35f090ec2022
-- title:
--   Replay: hist eq downset
-- statement:
--   Inside a configuration, the history of an event is its downset.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L152-L156
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean#L152-L156

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

theorem Replay.hist_eq_downset {c : Set es.Event} (hc : isConf es c) {x : es.Event} (hx : x ∈ c) :
    Stable.hist es.toFamily c x = downset es x := by sorry
