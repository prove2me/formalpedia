-- Prove2me | Theorems.Thm_ShannonColouring_card_misses_add
-- name    : ShannonColouring.card_misses_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:02:44.920575+00:00
-- url     : https://prove2.me/theorems/5e140e7f-47b7-5c6b-ba97-baa9b377c6ef
-- title:
--   Shannon Colouring: card misses add
-- statement:
--   Counting missing colours: at least `k` minus the number of edges at `x`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L69-L84
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L69-L84

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
omit [DecidableEq V] [Fintype ι]

theorem ShannonColouring.card_misses_add {k : ℕ} (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card +
      (s.filter fun i => Incident ends i x).card := by sorry
