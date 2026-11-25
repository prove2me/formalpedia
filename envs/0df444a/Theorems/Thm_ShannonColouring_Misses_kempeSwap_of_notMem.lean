-- Prove2me | Theorems.Thm_ShannonColouring_Misses_kempeSwap_of_notMem
-- name    : ShannonColouring.Misses.kempeSwap_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:12:16.718813+00:00
-- url     : https://prove2.me/theorems/d368871c-eb5d-434c-a07f-c6b5435639fa
-- title:
--   Misses: kempe Swap of not Mem
-- statement:
--   Outside `T`, missing colours are unchanged by a Kempe change.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L224-L232
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L224-L232

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

theorem ShannonColouring.Misses.kempeSwap_of_notMem {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∉ T) {δ : Fin k}
    (h : Misses ends s c x δ) : Misses ends s (kempeSwap ends c α γ T) x δ := by sorry
