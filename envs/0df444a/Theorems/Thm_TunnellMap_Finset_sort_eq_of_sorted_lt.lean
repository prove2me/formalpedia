-- Prove2me | Theorems.Thm_TunnellMap_Finset_sort_eq_of_sorted_lt
-- name    : TunnellMap.Finset.sort_eq_of_sorted_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:15.289052+00:00
-- url     : https://prove2.me/theorems/16651760-bdd8-42eb-8e5c-10f4ac361af8
-- title:
--   Finset: sort eq of sorted lt
-- statement:
--   A strictly increasing list whose members are exactly the members of a
--   finite set *is* the sorted list of that set.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L188-L196
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L188-L196

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap
variable {α : Type*}

theorem TunnellMap.Finset.sort_eq_of_sorted_lt {β : Type*} [LinearOrder β] (s : Finset β)
    (l : List β) (hs : l.Pairwise (· < ·)) (hmem : ∀ x, x ∈ l ↔ x ∈ s) :
    s.sort (· ≤ ·) = l := by sorry
