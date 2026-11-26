-- Prove2me | Theorems.Thm_TunnellMap_isortB_perm
-- name    : TunnellMap.isortB_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:37.843806+00:00
-- url     : https://prove2.me/theorems/8f953f2f-c77a-44e7-9a3b-668083bea75e
-- title:
--   Tunnell Map: isort B perm
-- statement:
--   The Tunnell Map construction uses the isort B perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L129-L132
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L129-L132

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.isortB_perm (le : α → α → Bool) (l : List α) : (isortB le l).Perm l := by sorry
