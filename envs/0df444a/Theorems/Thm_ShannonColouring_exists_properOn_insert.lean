-- Prove2me | Theorems.Thm_ShannonColouring_exists_properOn_insert
-- name    : ShannonColouring.exists_properOn_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:21:52.051128+00:00
-- url     : https://prove2.me/theorems/bd1a5902-8577-541b-a8d3-e1e733fdf18b
-- title:
--   Shannon Colouring: exists proper On insert
-- statement:
--   The induction step of Shannon's theorem: a proper colouring of `s` with `k` colours,
--   `3Δ ≤ 2k + 1`, can be modified into a proper colouring of `insert e s`.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L106-L234
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Shannon.lean#L106-L234

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]

theorem ShannonColouring.exists_properOn_insert [Fintype V] {k Δ : ℕ} {ends : ι → V × V}
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ Δ) (hk : 3 * Δ ≤ 2 * k + 1)
    {s : Finset ι} {e : ι} (he : e ∉ s) {c : ι → Fin k} (hc : ProperOn ends s c) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by sorry
