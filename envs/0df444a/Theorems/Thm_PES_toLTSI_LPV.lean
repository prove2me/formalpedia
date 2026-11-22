-- Prove2me | Theorems.Thm_PES_toLTSI_LPV
-- name    : PES.toLTSI_LPV
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:09:35.04234+00:00
-- url     : https://prove2.me/theorems/ebbcf823-5228-4e8c-9571-48035b6b28b0
-- title:
--   PES: to LTSI LPV
-- statement:
--   The event-structure LTSI satisfies LPV.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L72-L73
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L72-L73

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_ConfFamily_toLTSI_LPV

set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent

theorem PES.toLTSI_LPV : LTSI.LPV (toLTSI es) := by sorry
