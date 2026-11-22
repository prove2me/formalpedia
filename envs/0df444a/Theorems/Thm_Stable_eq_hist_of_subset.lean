-- Prove2me | Theorems.Thm_Stable_eq_hist_of_subset
-- name    : Stable.eq_hist_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:47.780769+00:00
-- url     : https://prove2.me/theorems/0e7896dd-65fb-459e-99d0-d4286422588c
-- title:
--   Stable: eq hist of subset
-- statement:
--   Inside a configuration, a prime is the history of its top.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L199-L205
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L199-L205

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.eq_hist_of_subset (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {p : Prime F} (hp : p.val ⊆ c) : p.val = hist F c (Prime.top p) := by sorry
