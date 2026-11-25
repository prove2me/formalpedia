-- Prove2me | Theorems.Thm_ShannonColouring_shannonTriangle_not_colourable
-- name    : ShannonColouring.shannonTriangle_not_colourable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:51:26.874236+00:00
-- url     : https://prove2.me/theorems/2648c742-0888-4512-a20b-3910820e9d94
-- title:
--   Shannon Colouring: shannon Triangle not colourable
-- statement:
--   A proper edge colouring of the Shannon triangle needs at least `⌊3Δ/2⌋` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L58-L67
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L58-L67

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.shannonTriangle_not_colourable (Δ k : ℕ) (hk : k < 3 * Δ / 2) :
    ¬ ∃ c : ShannonTriangleEdge Δ → Fin k, IsProperEdgeColouring (shannonTriangle Δ) c := by sorry
