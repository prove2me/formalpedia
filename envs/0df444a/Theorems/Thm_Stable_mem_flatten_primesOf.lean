-- Prove2me | Theorems.Thm_Stable_mem_flatten_primesOf
-- name    : Stable.mem_flatten_primesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:29.578017+00:00
-- url     : https://prove2.me/theorems/07f54fae-4d85-492c-b007-f8cfc0c2a133
-- title:
--   Stable: mem flatten primes Of
-- statement:
--   Every event of a configuration is the top of a prime inside it.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L186-L189
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L186-L189

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.mem_flatten_primesOf (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {x : F.Event} (hx : x ∈ c) : x ∈ flatten F (primesOf F c) := by sorry
