-- Prove2me | Theorems.Thm_SES_exists_least_enabling
-- name    : SES.exists_least_enabling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:19.236519+00:00
-- url     : https://prove2.me/theorems/69d25394-24c9-47cd-8b5a-d7259b62ea0d
-- title:
--   SES: exists least enabling
-- statement:
--   Inside a bound `z`, an event has a least enabling set.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L72-L94
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean#L72-L94

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable
set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
variable {S}

theorem SES.exists_least_enabling {z : Set S.Event} (hz : S.toGES.isConf z) {e : S.Event}
    {X₀ : Finset S.Event} (hX₀ : X₀ ⊢ e) (hX₀z : ↑X₀ ⊆ z) (hez : e ∈ z) :
    ∃ M : Finset S.Event, (M ⊢ e) ∧ M ⊆ X₀ ∧
      ∀ Y : Finset S.Event, (Y ⊢ e) → ↑Y ⊆ z → M ⊆ Y := by sorry
