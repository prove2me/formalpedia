-- Prove2me | Theorems.Thm_ShannonColouring_singleEdge_not_colourable_zero
-- name    : ShannonColouring.singleEdge_not_colourable_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:51:32.06342+00:00
-- url     : https://prove2.me/theorems/fbe02947-55ab-53c6-a619-294771ad703f
-- title:
--   Shannon Colouring: single Edge not colourable zero
-- statement:
--   The Shannon Colouring construction uses the single Edge not colourable zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L56-L58
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sanity.lean#L56-L58

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.singleEdge_not_colourable_zero :
    ¬ ∃ c : Unit → Fin 0, IsProperEdgeColouring singleEdge c := by sorry
