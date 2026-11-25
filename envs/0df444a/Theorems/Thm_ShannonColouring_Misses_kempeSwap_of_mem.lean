-- Prove2me | Theorems.Thm_ShannonColouring_Misses_kempeSwap_of_mem
-- name    : ShannonColouring.Misses.kempeSwap_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:12:08.270303+00:00
-- url     : https://prove2.me/theorems/1124e6ff-6182-4db3-9798-1e390cb28a7f
-- title:
--   Misses: kempe Swap of mem
-- statement:
--   Inside `T`, a Kempe change swaps the missing colours `α` and `γ`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L235-L249
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L235-L249

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

theorem ShannonColouring.Misses.kempeSwap_of_mem {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∈ T) {δ : Fin k}
    (h : Misses ends s c x (Equiv.swap α γ δ)) : Misses ends s (kempeSwap ends c α γ T) x δ := by sorry
