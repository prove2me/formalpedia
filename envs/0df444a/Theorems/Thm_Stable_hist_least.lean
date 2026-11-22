-- Prove2me | Theorems.Thm_Stable_hist_least
-- name    : Stable.hist_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:38:48.83397+00:00
-- url     : https://prove2.me/theorems/065ffd9d-52a1-4e53-8287-bc2e2e1c0c5c
-- title:
--   Stable: hist least
-- statement:
--   Any subconfiguration of `c` containing `x` contains its history.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Basic.lean#L105-L107
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Basic.lean#L105-L107

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*}
open Stable
variable {F : ConfFamily L}
variable {c : Set F.Event} {x : F.Event}

theorem Stable.hist_least {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hxm : x ∈ m) :
    hist F c x ⊆ m := by sorry
