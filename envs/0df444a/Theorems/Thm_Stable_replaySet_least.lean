-- Prove2me | Theorems.Thm_Stable_replaySet_least
-- name    : Stable.replaySet_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:06:27.726057+00:00
-- url     : https://prove2.me/theorems/0cefd1c5-5df7-4514-a5b7-60d931a73cbd
-- title:
--   Stable: replay Set least
-- statement:
--   It is least among subconfigurations of `c` containing `l`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L42-L46
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L42-L46

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
omit hc hlc

theorem Stable.replaySet_least {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hlm : l ⊆ m) :
    replaySet F c l ⊆ m := by sorry
