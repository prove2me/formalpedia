-- Prove2me | Theorems.Thm_ShannonColouring_card_incident_lt
-- name    : ShannonColouring.card_incident_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:02:41.129142+00:00
-- url     : https://prove2.me/theorems/0aeb10ab-7c69-5222-9029-77fb86b46e9f
-- title:
--   Shannon Colouring: card incident lt
-- statement:
--   If the edge `e ∉ s` is at `x`, then `s` has fewer edges at `x` than the degree of `x`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L52-L65
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L52-L65

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.card_incident_lt (ends : ι → V × V) {s : Finset ι} {e : ι} (he : e ∉ s) {x : V}
    (hex : Incident ends e x) :
    (s.filter fun i => Incident ends i x).card + 1 ≤ degree ends x := by sorry
