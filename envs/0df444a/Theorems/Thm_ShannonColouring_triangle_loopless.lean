-- Prove2me | Theorems.Thm_ShannonColouring_triangle_loopless
-- name    : ShannonColouring.triangle_loopless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:23.566538+00:00
-- url     : https://prove2.me/theorems/8968cff1-4f94-5fba-ad4c-6ef4e1301624
-- title:
--   Shannon Colouring: triangle loopless
-- statement:
--   The Shannon Colouring construction uses the triangle loopless property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L65-L66
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L65-L66

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.triangle_loopless (i : Fin 3) : (triangle i).1 ≠ (triangle i).2 := by sorry
