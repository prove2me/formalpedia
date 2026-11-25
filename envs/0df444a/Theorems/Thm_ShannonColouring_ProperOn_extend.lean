-- Prove2me | Theorems.Thm_ShannonColouring_ProperOn_extend
-- name    : ShannonColouring.ProperOn.extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:20:43.848112+00:00
-- url     : https://prove2.me/theorems/44ab9bac-1f0a-4247-8387-c5671ed5bb9d
-- title:
--   Proper On: extend
-- statement:
--   Colouring a new edge with a colour missing at both of its ends.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L43-L65
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L43-L65

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

theorem ShannonColouring.ProperOn.extend [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e : ι}
    (he : e ∉ s) {δ : Fin k} (h1 : Misses ends s c (ends e).1 δ)
    (h2 : Misses ends s c (ends e).2 δ) : ProperOn ends (insert e s) (Function.update c e δ) := by sorry
