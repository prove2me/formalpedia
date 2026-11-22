-- Prove2me | Theorems.Thm_PES_toFamily_Config
-- name    : PES.toFamily_Config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:21.797287+00:00
-- url     : https://prove2.me/theorems/df020efb-8ecf-40d0-b66c-335c67fcbb78
-- title:
--   PES: to Family Config
-- statement:
--   The PES construction uses the to Family Config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L136-L136
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L136-L136

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

theorem PES.toFamily_Config : P.toFamily.Config = isConf P := by sorry

attribute [defeq] PES.toFamily_Config
