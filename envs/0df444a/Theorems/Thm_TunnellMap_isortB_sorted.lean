-- Prove2me | Theorems.Thm_TunnellMap_isortB_sorted
-- name    : TunnellMap.isortB_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:39.620891+00:00
-- url     : https://prove2.me/theorems/990da88d-6bd8-4771-8d59-70fd91130e00
-- title:
--   Tunnell Map: isort B sorted
-- statement:
--   The Tunnell Map construction uses the isort B sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L158-L164
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L158-L164

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.isortB_sorted (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (l : List α) : (isortB le l).Pairwise fun x y => le x y = true := by sorry
