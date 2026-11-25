-- Prove2me | Theorems.Thm_ShannonColouring_shannonTriangle_three_not_colourable
-- name    : ShannonColouring.shannonTriangle_three_not_colourable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:58:50.803802+00:00
-- url     : https://prove2.me/theorems/6cade01d-3443-5320-9528-0936db44c50c
-- title:
--   Shannon Colouring: shannon Triangle three not colourable
-- statement:
--   The Shannon Colouring construction uses the shannon Triangle three not colourable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L96-L98
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L96-L98

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.shannonTriangle_three_not_colourable :
    ¬ ∃ c : ShannonTriangleEdge 3 → Fin 3, IsProperEdgeColouring (shannonTriangle 3) c := by sorry
