-- Prove2me | Theorems.Thm_Stable_flatten_insert
-- name    : Stable.flatten_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:49.605875+00:00
-- url     : https://prove2.me/theorems/72679c00-29ad-4567-8f01-6c090c1501b9
-- title:
--   Stable: flatten insert
-- statement:
--   Firing a prime adds exactly its top.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L262-L272
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L262-L272

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.flatten_insert (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    flatten F (c ∪ {p}) = flatten F c ∪ {Prime.top p} := by sorry
