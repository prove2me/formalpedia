-- Prove2me | Theorems.Thm_PES_toRLTSI_LPV
-- name    : PES.toRLTSI_LPV
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:09:39.245958+00:00
-- url     : https://prove2.me/theorems/d7ad2fd3-7271-4370-b855-7543ad64339a
-- title:
--   PES: to RLTSI LPV
-- statement:
--   Prime event structures are stable, so the reverse LPV axioms hold.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L88-L89
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean#L88-L89

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_ConfFamily_toRLTSI_LPV

set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent

theorem PES.toRLTSI_LPV : RLTSI.LPV (toRLTSI es) := by sorry
