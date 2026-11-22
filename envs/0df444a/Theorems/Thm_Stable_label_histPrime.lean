-- Prove2me | Theorems.Thm_Stable_label_histPrime
-- name    : Stable.label_histPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:30.604399+00:00
-- url     : https://prove2.me/theorems/6f0297cd-5d54-4674-a529-7f08dd2a4bc0
-- title:
--   Stable: label hist Prime
-- statement:
--   The label of a history-prime is the label of the event it is the history of.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L235-L239
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L235-L239

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.label_histPrime (hF : Stable F) (hcf : CoincidenceFree F) {c : Set F.Event}
    (hc : F.Config c) {x : F.Event} (hx : x ∈ c) :
    (toPES F).label (histPrime hF hc hx) = F.label x := by sorry
