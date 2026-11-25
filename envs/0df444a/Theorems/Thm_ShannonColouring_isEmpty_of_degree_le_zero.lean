-- Prove2me | Theorems.Thm_ShannonColouring_isEmpty_of_degree_le_zero
-- name    : ShannonColouring.isEmpty_of_degree_le_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:44:56.338383+00:00
-- url     : https://prove2.me/theorems/ece448a0-a50d-4e96-8b94-0e8af7f49fe5
-- title:
--   Shannon Colouring: is Empty of degree le zero
-- statement:
--   A multigraph of maximum degree `0` has no edges (Shannon's theorem gives a colouring with
--   `0` colours).
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L33-L37
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L33-L37

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.isEmpty_of_degree_le_zero {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 0) :
    IsEmpty ι := by sorry
