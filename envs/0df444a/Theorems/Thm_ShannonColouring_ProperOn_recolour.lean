-- Prove2me | Theorems.Thm_ShannonColouring_ProperOn_recolour
-- name    : ShannonColouring.ProperOn.recolour
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:02:48.132807+00:00
-- url     : https://prove2.me/theorems/0116f1ca-83d8-4578-8b2c-5dcf580ebd30
-- title:
--   Proper On: recolour
-- statement:
--   Recolouring an edge with a colour missing at both of its ends.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L68-L74
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L68-L74

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

theorem ShannonColouring.ProperOn.recolour [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {f : ι}
    (hf : f ∈ s) {δ : Fin k} (hδ : ∀ x, Incident ends f x → Misses ends s c x δ) :
    ProperOn ends s (Function.update c f δ) := by sorry
