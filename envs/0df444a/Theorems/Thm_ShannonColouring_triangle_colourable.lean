-- Prove2me | Theorems.Thm_ShannonColouring_triangle_colourable
-- name    : ShannonColouring.triangle_colourable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:52:13.720246+00:00
-- url     : https://prove2.me/theorems/b2183f18-f2fb-5b50-9e0f-50e447e2c290
-- title:
--   Shannon Colouring: triangle colourable
-- statement:
--   Shannon's theorem colours the triangle with `⌊3·2/2⌋ = 3` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L72-L73
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L72-L73

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.triangle_colourable : ∃ c : Fin 3 → Fin 3, IsProperEdgeColouring triangle c := by sorry
