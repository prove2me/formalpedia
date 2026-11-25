-- Prove2me | Theorems.Thm_ShannonColouring_card_misses_ge
-- name    : ShannonColouring.card_misses_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:12:49.236106+00:00
-- url     : https://prove2.me/theorems/b20a0f9c-7c62-476a-ae19-2f2a6aca284f
-- title:
--   Shannon Colouring: card misses ge
-- statement:
--   A vertex `x` misses at least `k - Δ` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L87-L93
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L87-L93

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.card_misses_ge {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by sorry
