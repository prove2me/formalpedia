-- Prove2me | Theorems.Thm_ShannonColouring_card_shannonTriangleEdge_one
-- name    : ShannonColouring.card_shannonTriangleEdge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:53:12.506604+00:00
-- url     : https://prove2.me/theorems/2eb025e9-9edc-5a89-b07d-9627245e8b73
-- title:
--   Shannon Colouring: card shannon Triangle Edge one
-- statement:
--   For `Δ = 1` the Shannon triangle is a single edge.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L88-L88
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L88-L88

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.card_shannonTriangleEdge_one : Fintype.card (ShannonTriangleEdge 1) = 1 := by sorry
