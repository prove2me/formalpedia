-- Prove2me | Theorems.Thm_TunnellMap_insertB_sorted
-- name    : TunnellMap.insertB_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:55.943258+00:00
-- url     : https://prove2.me/theorems/07f984b2-4cb4-541d-ba21-cac1069682e4
-- title:
--   Tunnell Map: insert B sorted
-- statement:
--   The Tunnell Map construction uses the insert B sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L134-L156
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L134-L156

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.insertB_sorted (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (a : α) {l : List α} (hl : l.Pairwise fun x y => le x y = true) :
    (insertB le a l).Pairwise fun x y => le x y = true := by sorry
