-- Prove2me | Theorems.Thm_ShannonColouring_kempeGraph_adj_ends
-- name    : ShannonColouring.kempeGraph_adj_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:03:20.898983+00:00
-- url     : https://prove2.me/theorems/04ccc7d8-64cd-4327-bda2-9d1d13505926
-- title:
--   Shannon Colouring: kempe Graph adj ends
-- statement:
--   The Shannon Colouring construction uses the kempe Graph adj ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L116-L119
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean#L116-L119

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

theorem ShannonColouring.kempeGraph_adj_ends (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} {i : ι} (hi : i ∈ s) (hc : c i = α ∨ c i = γ) :
    (kempeGraph ends s c α γ).Adj (ends i).1 (ends i).2 := by sorry
