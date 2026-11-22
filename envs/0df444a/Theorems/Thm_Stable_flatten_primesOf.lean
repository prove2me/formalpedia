-- Prove2me | Theorems.Thm_Stable_flatten_primesOf
-- name    : Stable.flatten_primesOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:51:47.193604+00:00
-- url     : https://prove2.me/theorems/cee9f73d-73aa-4c52-b112-7f59ec6d3e4c
-- title:
--   Stable: flatten primes Of
-- statement:
--   Flattening recovers the configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L192-L196
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L192-L196

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.flatten_primesOf (hF : Stable F) {c : Set F.Event} (hc : F.Config c) :
    flatten F (primesOf F c) = c := by sorry
