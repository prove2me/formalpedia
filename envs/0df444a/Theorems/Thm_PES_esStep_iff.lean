-- Prove2me | Theorems.Thm_PES_esStep_iff
-- name    : PES.esStep_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:24.720814+00:00
-- url     : https://prove2.me/theorems/999f5a5a-0112-4e71-ae48-022b069c7842
-- title:
--   PES: es Step iff
-- statement:
--   The prime and family step relations agree.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L43-L49
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L43-L49

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent

theorem PES.esStep_iff {c₁ c₂ : Conf es} {a : L} :
    ConfFamily.esStep es.toFamily c₁ a c₂ ↔ esStep es c₁ a c₂ := by sorry
