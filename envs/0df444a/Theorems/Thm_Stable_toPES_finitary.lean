-- Prove2me | Theorems.Thm_Stable_toPES_finitary
-- name    : Stable.toPES_finitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:51:32.539884+00:00
-- url     : https://prove2.me/theorems/f114684a-cf3c-414a-a0b0-221cd92ec48e
-- title:
--   Stable: to PES finitary
-- statement:
--   The prime event structure of complete primes has finite causes.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L208-L222
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L208-L222

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.toPES_finitary (G : GES L) (hF : Stable G.toFamily) (p : (toPES G.toFamily).Event) :
    Set.Finite ((toPES G.toFamily).past p) := by sorry
