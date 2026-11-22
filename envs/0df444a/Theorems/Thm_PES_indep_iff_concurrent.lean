-- Prove2me | Theorems.Thm_PES_indep_iff_concurrent
-- name    : PES.indep_iff_concurrent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:10.426796+00:00
-- url     : https://prove2.me/theorems/7e9dbd7e-2ec5-43de-a877-1387e475e072
-- title:
--   PES: indep iff concurrent
-- statement:
--   Derived independence coincides with concurrency, for distinct fresh events.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L153-L185
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L153-L185

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

theorem PES.indep_iff_concurrent {c : Set P.Event} {e₁ e₂ : P.Event}
    (h₁ : Configuration.enables P c e₁) (h₂ : Configuration.enables P c e₂)
    (hf₁ : e₁ ∉ c) (hf₂ : e₂ ∉ c) :
    P.toFamily.Indep c e₁ e₂ ↔ P.concurrent e₁ e₂ := by sorry
