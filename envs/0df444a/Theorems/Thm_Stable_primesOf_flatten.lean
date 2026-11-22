-- Prove2me | Theorems.Thm_Stable_primesOf_flatten
-- name    : Stable.primesOf_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:23.597677+00:00
-- url     : https://prove2.me/theorems/7ee06edd-70a8-452a-b9be-9f1a3a86b2c3
-- title:
--   Stable: primes Of flatten
-- statement:
--   A set of primes whose union is a configuration is recovered from it.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L225-L232
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L225-L232

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.primesOf_flatten (hF : Stable F) {S : Set (Prime F)}
    (hS : isConf (toPES F) S) (hflat : F.Config (flatten F S)) :
    primesOf F (flatten F S) = S := by sorry
