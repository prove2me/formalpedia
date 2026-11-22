-- Prove2me | Theorems.Thm_Stable_prime_val_finite
-- name    : Stable.prime_val_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:21.301079+00:00
-- url     : https://prove2.me/theorems/eaa735a9-8a5b-4a18-949d-4a039a01fc21
-- title:
--   Stable: prime val finite
-- statement:
--   Complete primes have finite carriers.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L164-L166
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L164-L166

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.prime_val_finite (G : GES L) (hF : Stable G.toFamily) (p : Prime G.toFamily) :
    p.val.Finite := by sorry
