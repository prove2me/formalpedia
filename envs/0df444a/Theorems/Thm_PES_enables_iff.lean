-- Prove2me | Theorems.Thm_PES_enables_iff
-- name    : PES.enables_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:11.513915+00:00
-- url     : https://prove2.me/theorems/53e0da40-9acc-4c68-8ba4-28a398007b19
-- title:
--   PES: enables iff
-- statement:
--   The family enabling relation agrees with the prime one.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L139-L149
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L139-L149

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

theorem PES.enables_iff {c : Set P.Event} {e : P.Event} :
    P.toFamily.enables c e ↔ Configuration.enables P c e := by sorry
