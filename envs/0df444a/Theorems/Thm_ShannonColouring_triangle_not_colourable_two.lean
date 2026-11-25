-- Prove2me | Theorems.Thm_ShannonColouring_triangle_not_colourable_two
-- name    : ShannonColouring.triangle_not_colourable_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:53:05.477401+00:00
-- url     : https://prove2.me/theorems/91e6575d-7ec4-45fb-a324-596cb33b1859
-- title:
--   Shannon Colouring: triangle not colourable two
-- statement:
--   The triangle has no proper edge colouring with `2` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L76-L83
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L76-L83

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.triangle_not_colourable_two : ¬ ∃ c : Fin 3 → Fin 2, IsProperEdgeColouring triangle c := by sorry
