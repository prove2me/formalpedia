-- Prove2me | Theorems.Thm_Stable_Prime_top_mem
-- name    : Stable.Prime.top_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:30.202248+00:00
-- url     : https://prove2.me/theorems/b99042ee-825b-46dd-919a-0f648930bab3
-- title:
--   Prime: top mem
-- statement:
--   The Prime construction uses the top mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L109-L109
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L109-L109

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime

theorem Stable.Prime.top_mem (p : Prime F) : top p ∈ p.val := by sorry
