-- Prove2me | Theorems.Thm_PES_esIndep_iff
-- name    : PES.esIndep_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:42:26.754147+00:00
-- url     : https://prove2.me/theorems/fc479f7c-7c5f-4eb8-bdf3-6451aec76593
-- title:
--   PES: es Indep iff
-- statement:
--   The prime and family independence relations agree.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L52-L62
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L52-L62

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

theorem PES.esIndep_iff {c c₁ c₂ : Conf es} {a b : L} :
    ConfFamily.esIndep es.toFamily c a c₁ b c₂ ↔ esIndep es c a c₁ b c₂ := by sorry
