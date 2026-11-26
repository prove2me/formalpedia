-- Prove2me | Theorems.Thm_UntimedCrossings_nodup_of_fixed_endpoint
-- name    : UntimedCrossings.nodup_of_fixed_endpoint
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:08:57.945802+00:00
-- url     : https://prove2.me/theorems/4d146c0d-eb45-4740-a4aa-2206f17ef862
-- title:
--   A deterministic run with a fixed endpoint never repeats a crossing destination
-- statement:
--   Label the states of a deterministic system by two sides. In a finite run ending at a fixed point of its transition, the states entered at crossings form a list with no duplicates.
-- source:
--   A termination property of the deterministic crossing records used in the crossing-sequence method.

import Definitions.Def_UntimedEndpointExchange

open UntimedCrossings

set_option autoImplicit false

theorem UntimedCrossings.nodup_of_fixed_endpoint {S : Type*} (side : S → Bool)
    (step : S → S) (z : S) (T : ℕ)
    (settled : step (step^[T] z) = step^[T] z) :
    (untimedRecord side step z T).Nodup := by sorry
