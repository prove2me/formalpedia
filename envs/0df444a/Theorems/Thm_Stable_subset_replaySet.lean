-- Prove2me | Theorems.Thm_Stable_subset_replaySet
-- name    : Stable.subset_replaySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:06:13.968883+00:00
-- url     : https://prove2.me/theorems/92894e3b-c266-4124-adbe-33e5ca724429
-- title:
--   Stable: subset replay Set
-- statement:
--   The Stable construction uses the subset replay Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L22-L23
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean#L22-L23

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
omit hc hlc

theorem Stable.subset_replaySet : l ⊆ replaySet F c l := by sorry
