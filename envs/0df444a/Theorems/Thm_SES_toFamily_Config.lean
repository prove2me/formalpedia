-- Prove2me | Theorems.Thm_SES_toFamily_Config
-- name    : SES.toFamily_Config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:38:58.177892+00:00
-- url     : https://prove2.me/theorems/3efd9e79-515c-45d9-8a2e-d5a262cdf73e
-- title:
--   SES: to Family Config
-- statement:
--   The SES construction uses the to Family Config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L24-L24
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L24-L24

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable
import Theorems.Thm_GES_toFamily_Config
attribute [local simp] GES.toFamily_Config


set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable

theorem SES.toFamily_Config : S.toFamily.Config = S.toGES.isConf := by sorry

attribute [defeq] SES.toFamily_Config
