-- Prove2me | Theorems.Thm_ShannonColouring_ProperOn_recolour_extend
-- name    : ShannonColouring.ProperOn.recolour_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:02:25.334713+00:00
-- url     : https://prove2.me/theorems/d4872f18-f15f-5d5f-bdc1-c8c9e2080c0b
-- title:
--   Proper On: recolour extend
-- statement:
--   Recolour an edge `f` at `u` from `β` to `α` (missing at both ends of `f`), and then colour the
--   new edge `e = uv` with `β`, assuming `β` is missing at `v`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L83-L102
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L83-L102

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

theorem ShannonColouring.ProperOn.recolour_extend [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e f : ι}
    (he : e ∉ s) (hf : f ∈ s) {α β : Fin k} (hfu : Incident ends f (ends e).1) (hcf : c f = β)
    (hα : ∀ x, Incident ends f x → Misses ends s c x α) (hβ : Misses ends s c (ends e).2 β) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by sorry
