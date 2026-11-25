-- Prove2me | Theorems.Thm_ShannonColouring_ProperOn_mono
-- name    : ShannonColouring.ProperOn.mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:52:27.513355+00:00
-- url     : https://prove2.me/theorems/591bffc0-93f3-52b5-ba63-3507ad7b6b3e
-- title:
--   Proper On: mono
-- statement:
--   The Proper On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L36-L37
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L36-L37

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

theorem ShannonColouring.ProperOn.mono {s t : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) (hts : t ⊆ s) :
    ProperOn ends t c := by sorry
