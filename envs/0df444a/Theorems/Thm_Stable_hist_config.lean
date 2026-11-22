-- Prove2me | Theorems.Thm_Stable_hist_config
-- name    : Stable.hist_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:39:04.874128+00:00
-- url     : https://prove2.me/theorems/ea37d889-175b-4d40-938b-7d9878009ff4
-- title:
--   Stable: hist config
-- statement:
--   The history is itself a configuration, because of stability.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Basic.lean#L110-L112
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Basic.lean#L110-L112

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

theorem Stable.hist_config (hF : Stable F) (hc : F.Config c) (hx : x ∈ c) :
    F.Config (hist F c x) := by sorry
