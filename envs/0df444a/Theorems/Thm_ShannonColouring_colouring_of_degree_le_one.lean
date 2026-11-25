-- Prove2me | Theorems.Thm_ShannonColouring_colouring_of_degree_le_one
-- name    : ShannonColouring.colouring_of_degree_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:45:21.497852+00:00
-- url     : https://prove2.me/theorems/c50950e1-32e7-4e52-b436-49eacb2fe614
-- title:
--   Shannon Colouring: colouring of degree le one
-- statement:
--   A multigraph of maximum degree `1` (a matching) can be properly coloured with one colour.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L42-L45
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L42-L45

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.colouring_of_degree_le_one {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 1) :
    ∃ c : ι → Fin 1, IsProperEdgeColouring ends c := by sorry
