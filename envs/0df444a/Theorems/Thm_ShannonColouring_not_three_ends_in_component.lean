-- Prove2me | Theorems.Thm_ShannonColouring_not_three_ends_in_component
-- name    : ShannonColouring.not_three_ends_in_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:42:24.986534+00:00
-- url     : https://prove2.me/theorems/491d6954-35f5-4acc-b04e-6d15f3715c86
-- title:
--   Shannon Colouring: not three ends in component
-- statement:
--   In a finite simple graph of maximum degree at most `2`, three distinct vertices of degree at
--   most `1` can not lie in a common connected component.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/PathEnds.lean#L27-L79
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/PathEnds.lean#L27-L79

module
public import Mathlib
public import Definitions.Def_ShannonColouring_PathEnds
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open SimpleGraph

theorem ShannonColouring.not_three_ends_in_component {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hdeg : ∀ x, H.degree x ≤ 2) {u v w : V} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hv : H.Reachable u v) (hw : H.Reachable u w) (du : H.degree u ≤ 1)
    (dv : H.degree v ≤ 1) (dw : H.degree w ≤ 1) : False := by sorry
