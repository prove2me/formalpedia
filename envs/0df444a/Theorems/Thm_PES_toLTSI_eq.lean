-- Prove2me | Theorems.Thm_PES_toLTSI_eq
-- name    : PES.toLTSI_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:45:56.164982+00:00
-- url     : https://prove2.me/theorems/f7837c5d-c87c-4750-a849-69c1ae362afd
-- title:
--   PES: to LTSI eq
-- statement:
--   The prime LTSI *is* the family LTSI.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L65-L69
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L65-L69

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

theorem PES.toLTSI_eq : toLTSI es = ConfFamily.toLTSI es.toFamily := by sorry
