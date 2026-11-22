-- Prove2me | Theorems.Thm_Stable_histPrime_lt
-- name    : Stable.histPrime_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:25.064255+00:00
-- url     : https://prove2.me/theorems/e0287546-97ee-4d85-b8c6-b45dd3117f97
-- title:
--   Stable: hist Prime lt
-- statement:
--   A non-top event of a prime is the top of a strictly smaller prime.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L246-L250
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L246-L250

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.histPrime_lt (hF : Stable F) (hcf : CoincidenceFree F) (p : Prime F)
    {t : F.Event} (ht : t ∈ p.val) (hne : t ≠ Prime.top p) :
    histPrime hF p.config ht < p := by sorry
