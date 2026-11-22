-- Prove2me | Theorems.Thm_Stable_val_subset_flatten
-- name    : Stable.val_subset_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:40.376264+00:00
-- url     : https://prove2.me/theorems/a4746dba-bcdf-4ce5-9d2e-12ac46cfcc6c
-- title:
--   Stable: val subset flatten
-- statement:
--   Every event of an enabled prime other than its top is already present.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L253-L259
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L253-L259

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.val_subset_flatten (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    p.val ⊆ flatten F c ∪ {Prime.top p} := by sorry
