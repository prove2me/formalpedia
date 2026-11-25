-- Prove2me | Theorems.Thm_ShannonColouring_card_shannonTriangleEdge
-- name    : ShannonColouring.card_shannonTriangleEdge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:51:30.15225+00:00
-- url     : https://prove2.me/theorems/38e0f7ec-ff56-40d6-9093-ed9d4b8232d3
-- title:
--   Shannon Colouring: card shannon Triangle Edge
-- statement:
--   The Shannon Colouring construction uses the card shannon Triangle Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L53-L55
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L53-L55

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.card_shannonTriangleEdge (Δ : ℕ) : Fintype.card (ShannonTriangleEdge Δ) = 3 * Δ / 2 := by sorry
