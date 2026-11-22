-- Prove2me | Theorems.Thm_Stable_Prime_eq_top
-- name    : Stable.Prime.eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:44.487128+00:00
-- url     : https://prove2.me/theorems/60780fe8-93f6-4ed2-91cf-dc6f96439aa6
-- title:
--   Prime: eq top
-- statement:
--   Any event witnessing primeness is the greatest one.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L115-L122
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L115-L122

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime

theorem Stable.Prime.eq_top (hcf : CoincidenceFree F) (p : Prime F) {y : F.Event}
    (hy : y ∈ p.val) (hh : p.val = hist F p.val y) : y = top p := by sorry
