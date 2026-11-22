-- Prove2me | Theorems.Thm_Stable_Prime_le_iff
-- name    : Stable.Prime.le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:45:02.128259+00:00
-- url     : https://prove2.me/theorems/495139a3-385d-45cc-9fa9-ab08201c8fcd
-- title:
--   Prime: le iff
-- statement:
--   The Prime construction uses the le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L104-L104
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L104-L104

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime

theorem Stable.Prime.le_iff {p q : Prime F} : p ≤ q ↔ p.val ⊆ q.val := by sorry
