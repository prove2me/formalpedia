-- Prove2me | Theorems.Thm_TunnellMap_mergeSort_eq_isortB
-- name    : TunnellMap.mergeSort_eq_isortB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:03.191249+00:00
-- url     : https://prove2.me/theorems/1898aec3-1b2c-4cac-b28f-58d14f6f7cac
-- title:
--   Tunnell Map: merge Sort eq isort B
-- statement:
--   `List.mergeSort` and `isortB` agree on any list whose elements are
--   pairwise antisymmetric for the comparison.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L168-L182
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L168-L182

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.mergeSort_eq_isortB (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    {l : List α}
    (hanti : ∀ a ∈ l, ∀ b ∈ l, le a b = true → le b a = true → a = b) :
    l.mergeSort le = isortB le l := by sorry
