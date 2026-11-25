-- Prove2me | Theorems.Thm_ShannonColouring_shannonTriangle_adjacent
-- name    : ShannonColouring.shannonTriangle_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:51:37.423542+00:00
-- url     : https://prove2.me/theorems/16457483-b899-4d47-9810-d3ce89baada9
-- title:
--   Shannon Colouring: shannon Triangle adjacent
-- statement:
--   Any two edges of the Shannon triangle share an end.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L48-L51
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L48-L51

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.shannonTriangle_adjacent (Δ : ℕ) (i j : ShannonTriangleEdge Δ) :
    ∃ v, Incident (shannonTriangle Δ) i v ∧ Incident (shannonTriangle Δ) j v := by sorry
