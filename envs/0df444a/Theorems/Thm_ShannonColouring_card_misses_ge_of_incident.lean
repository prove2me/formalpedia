-- Prove2me | Theorems.Thm_ShannonColouring_card_misses_ge_of_incident
-- name    : ShannonColouring.card_misses_ge_of_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:12:38.148017+00:00
-- url     : https://prove2.me/theorems/3e7eb5cd-f580-5d9d-ab98-0ccf4f96dd35
-- title:
--   Shannon Colouring: card misses ge of incident
-- statement:
--   An end `x` of the new edge `e ∉ s` misses at least `k - Δ + 1` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L96-L102
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L96-L102

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.card_misses_ge_of_incident {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    {s : Finset ι} {e : ι} (he : e ∉ s) (c : ι → Fin k) {x : V} (hex : Incident ends e x) :
    k + 1 ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by sorry
