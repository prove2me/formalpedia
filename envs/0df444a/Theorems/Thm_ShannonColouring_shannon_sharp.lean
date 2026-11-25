-- Prove2me | Theorems.Thm_ShannonColouring_shannon_sharp
-- name    : ShannonColouring.shannon_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:51:27.85437+00:00
-- url     : https://prove2.me/theorems/9e5f2aac-ab80-4871-a02a-51436e265666
-- title:
--   Shannon Colouring: shannon sharp
-- statement:
--   **Sharpness of Shannon's theorem**: for every `Δ` the Shannon triangle is a loopless
--   multigraph of maximum degree at most `Δ` with no proper edge colouring with fewer than
--   `⌊3Δ/2⌋` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L72-L76
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean#L72-L76

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring

theorem ShannonColouring.shannon_sharp (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c := by sorry
