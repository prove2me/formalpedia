-- Prove2me | Theorems.Thm_PES_minimalConflict_minimal
-- name    : PES.minimalConflict_minimal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:46:47.783947+00:00
-- url     : https://prove2.me/theorems/ad8c92ea-587d-4699-b0f3-322df3ab1cdc
-- title:
--   PES: minimal Conflict minimal
-- statement:
--   A conflicting pair below a minimal conflict is that conflict.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L78-L81
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L78-L81

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic
set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent
local infixl:50 " ## " => es.minimalConflict

theorem PES.minimalConflict_minimal {e₁ e₂ e₁' e₂' : es.Event} (h : es.minimalConflict e₁ e₂)
    (he₁ : e₁' ≤ e₁) (he₂ : e₂' ≤ e₂) (hConf : es.conflict e₁' e₂') :
    e₁' = e₁ ∧ e₂' = e₂ := by sorry
