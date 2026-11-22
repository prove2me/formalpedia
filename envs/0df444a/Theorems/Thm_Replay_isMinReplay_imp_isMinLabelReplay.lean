-- Prove2me | Theorems.Thm_Replay_isMinReplay_imp_isMinLabelReplay
-- name    : Replay.isMinReplay_imp_isMinLabelReplay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:05:57.298387+00:00
-- url     : https://prove2.me/theorems/12e300aa-318d-4117-9e8e-f59442689c38
-- title:
--   Replay: is Min Replay imp is Min Label Replay
-- statement:
--   A least replay is least on labels too.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L60-L62
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L60-L62

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R

theorem Replay.isMinReplay_imp_isMinLabelReplay {l : Set F.Event} {σ : Computations F}
    (h : isMinReplay F R l σ) : isMinLabelReplay F R l σ := by sorry
