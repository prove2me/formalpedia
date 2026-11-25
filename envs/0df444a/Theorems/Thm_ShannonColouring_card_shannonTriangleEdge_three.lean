-- Prove2me | Theorems.Thm_ShannonColouring_card_shannonTriangleEdge_three
-- name    : ShannonColouring.card_shannonTriangleEdge_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:59:26.016269+00:00
-- url     : https://prove2.me/theorems/f4d5711b-03c0-4f57-9a42-99fd501f2a96
-- title:
--   Shannon Colouring: card shannon Triangle Edge three
-- statement:
--   For `Δ = 3` the Shannon triangle has multiplicities `1, 1, 2` and `4 = ⌊9/2⌋` edges.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L94-L94
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L94-L94

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.card_shannonTriangleEdge_three : Fintype.card (ShannonTriangleEdge 3) = 4 := by sorry
