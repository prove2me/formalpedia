-- Prove2me | Theorems.Thm_Stable_primesOf_isConf
-- name    : Stable.primesOf_isConf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:51:09.591893+00:00
-- url     : https://prove2.me/theorems/31ec33e8-cc78-48e2-99cb-54a45bce5998
-- title:
--   Stable: primes Of is Conf
-- statement:
--   Configurations map to configurations.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L181-L183
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L181-L183

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.primesOf_isConf {c : Set F.Event} (hc : F.Config c) :
    isConf (toPES F) (primesOf F c) := by sorry
