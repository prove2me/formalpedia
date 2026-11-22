-- Prove2me | Theorems.Thm_PES_toFamily_Event
-- name    : PES.toFamily_Event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:18.364799+00:00
-- url     : https://prove2.me/theorems/3cfd637d-b579-4bc1-bf89-9c52f95b204a
-- title:
--   PES: to Family Event
-- statement:
--   The PES construction uses the to Family Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L134-L134
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L134-L134

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
variable {L : Type*} (P : PES L)

theorem PES.toFamily_Event : P.toFamily.Event = P.Event := by sorry

attribute [defeq] PES.toFamily_Event
