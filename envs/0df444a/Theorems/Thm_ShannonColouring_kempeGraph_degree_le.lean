-- Prove2me | Theorems.Thm_ShannonColouring_kempeGraph_degree_le
-- name    : ShannonColouring.kempeGraph_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:11:51.777153+00:00
-- url     : https://prove2.me/theorems/076bb38b-808c-4fc3-bf25-1ac24672ecfa
-- title:
--   Shannon Colouring: kempe Graph degree le
-- statement:
--   The degree of a vertex in the Kempe graph is bounded by the number of available colours
--   among `α`, `γ` at that vertex.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L123-L161
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L123-L161

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}

theorem ShannonColouring.kempeGraph_degree_le [Fintype V] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c)
    {α γ : Fin k} [DecidableRel (kempeGraph ends s c α γ).Adj] (x : V) (D : Finset (Fin k))
    (hD : ∀ i ∈ s, Incident ends i x → (c i = α ∨ c i = γ) → c i ∈ D) :
    (kempeGraph ends s c α γ).degree x ≤ D.card := by sorry
