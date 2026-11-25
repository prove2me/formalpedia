-- Prove2me | Theorems.Thm_ShannonColouring_card_incident_le
-- name    : ShannonColouring.card_incident_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:11:59.117661+00:00
-- url     : https://prove2.me/theorems/c760ff8d-d2ff-5226-ab12-8e1ce0a7d97e
-- title:
--   Shannon Colouring: card incident le
-- statement:
--   The number of edges of `s` at `x` is at most the degree of `x`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L44-L49
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L44-L49

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.card_incident_le (ends : ι → V × V) (s : Finset ι) (x : V) :
    (s.filter fun i => Incident ends i x).card ≤ degree ends x := by sorry
