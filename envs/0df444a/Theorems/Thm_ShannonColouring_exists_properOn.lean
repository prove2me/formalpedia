-- Prove2me | Theorems.Thm_ShannonColouring_exists_properOn
-- name    : ShannonColouring.exists_properOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:21.069808+00:00
-- url     : https://prove2.me/theorems/6a5bea9c-85a8-49a2-8868-6451b1d4bd45
-- title:
--   Shannon Colouring: exists proper On
-- statement:
--   Every subset of the edges can be properly coloured with `⌊3Δ/2⌋` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L237-L250
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L237-L250

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.exists_properOn [Fintype V] {ends : ι → V × V} (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ)
    (hΔ : ∀ v, degree ends v ≤ Δ) (s : Finset ι) :
    ∃ c : ι → Fin (3 * Δ / 2), ProperOn ends s c := by sorry
