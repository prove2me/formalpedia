-- Prove2me | Theorems.Thm_TunnellMap_insertB_perm
-- name    : TunnellMap.insertB_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:25.523293+00:00
-- url     : https://prove2.me/theorems/2c5dec2c-e811-52a2-8f92-e10e72570470
-- title:
--   Tunnell Map: insert B perm
-- statement:
--   The Tunnell Map construction uses the insert B perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L119-L127
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L119-L127

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.insertB_perm (le : α → α → Bool) (a : α) (l : List α) :
    (insertB le a l).Perm (a :: l) := by sorry
