-- Prove2me | Theorems.Thm_SES_inter_isConf
-- name    : SES.inter_isConf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:49:08.197866+00:00
-- url     : https://prove2.me/theorems/7ff65a29-4126-4a1c-990c-42b61ee59b6e
-- title:
--   SES: inter is Conf
-- statement:
--   Bounded binary intersections of configurations are configurations.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L30-L69
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L30-L69

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable
set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
variable {S}
open GES

theorem SES.inter_isConf {x y z : Set S.Event} (hx : S.toGES.isConf x) (hy : S.toGES.isConf y)
    (hz : S.toGES.isConf z) (hxz : x ⊆ z) (hyz : y ⊆ z) : S.toGES.isConf (x ∩ y) := by sorry
