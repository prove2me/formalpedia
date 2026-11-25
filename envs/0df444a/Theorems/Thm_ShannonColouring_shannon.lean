-- Prove2me | Theorems.Thm_ShannonColouring_shannon
-- name    : ShannonColouring.shannon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:02:56.410971+00:00
-- url     : https://prove2.me/theorems/a2a8816f-87f6-424e-88bd-9e0b3e72480f
-- title:
--   Shannon Colouring: shannon
-- statement:
--   **Shannon's theorem** (1949): a loopless multigraph of maximum degree at most `Δ` has a
--   proper edge colouring with `⌊3Δ/2⌋` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L254-L258
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L254-L258

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.shannon {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c := by sorry
