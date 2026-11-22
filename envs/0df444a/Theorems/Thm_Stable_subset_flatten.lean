-- Prove2me | Theorems.Thm_Stable_subset_flatten
-- name    : Stable.subset_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:41.373807+00:00
-- url     : https://prove2.me/theorems/644938c8-9019-4e8d-950c-93719fc59627
-- title:
--   Stable: subset flatten
-- statement:
--   The Stable construction uses the subset flatten property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L176-L178
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L176-L178

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.subset_flatten {S : Set (Prime F)} {p : Prime F} (hp : p ∈ S) :
    p.val ⊆ flatten F S := by sorry
