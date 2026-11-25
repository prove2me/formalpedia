-- Prove2me | Theorems.Thm_ShannonColouring_shannonTriangle_loopless
-- name    : ShannonColouring.shannonTriangle_loopless
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:51:31.454653+00:00
-- url     : https://prove2.me/theorems/b4d7748f-3caf-4ee2-947b-5da11b1e77be
-- title:
--   Shannon Colouring: shannon Triangle loopless
-- statement:
--   The Shannon Colouring construction uses the shannon Triangle loopless property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L38-L40
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L38-L40

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.shannonTriangle_loopless (Δ : ℕ) (i : ShannonTriangleEdge Δ) :
    (shannonTriangle Δ i).1 ≠ (shannonTriangle Δ i).2 := by sorry
