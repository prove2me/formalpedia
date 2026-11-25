-- Prove2me | Theorems.Thm_ShannonColouring_kempeClosed_reachable
-- name    : ShannonColouring.kempeClosed_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:12:20.996695+00:00
-- url     : https://prove2.me/theorems/d7aa4656-8904-496f-aa27-fd9ee9313a26
-- title:
--   Shannon Colouring: kempe Closed reachable
-- statement:
--   The vertex set of the component of `z` in the Kempe graph is Kempe-closed.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L252-L257
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L252-L257

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

theorem ShannonColouring.kempeClosed_reachable (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} (z : V) :
    KempeClosed ends s c α γ {x | (kempeGraph ends s c α γ).Reachable z x} := by sorry
