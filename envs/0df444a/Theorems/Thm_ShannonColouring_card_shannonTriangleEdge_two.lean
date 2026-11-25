-- Prove2me | Theorems.Thm_ShannonColouring_card_shannonTriangleEdge_two
-- name    : ShannonColouring.card_shannonTriangleEdge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:53:57.838409+00:00
-- url     : https://prove2.me/theorems/6b898ab1-f0a6-40b1-b931-e191a028fe31
-- title:
--   Shannon Colouring: card shannon Triangle Edge two
-- statement:
--   For `Δ = 2` the Shannon triangle is the triangle `K₃`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L91-L91
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L91-L91

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.card_shannonTriangleEdge_two : Fintype.card (ShannonTriangleEdge 2) = 3 := by sorry
