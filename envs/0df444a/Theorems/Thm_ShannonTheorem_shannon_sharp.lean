-- Prove2me | Theorems.Thm_ShannonTheorem_shannon_sharp
-- name    : ShannonTheorem.shannon_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:02:17.550017+00:00
-- url     : https://prove2.me/theorems/20c50cb2-a7b9-4021-b37d-716d9fc9b46d
-- title:
--   Shannon Theorem: shannon sharp
-- statement:
--   **Sharpness of Shannon's theorem**: for every `Δ` there is a loopless multigraph on three
--   vertices of maximum degree at most `Δ` with no proper edge colouring with fewer than `⌊3Δ/2⌋`
--   colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/Solution.lean#L47-L50
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/Solution.lean#L47-L50

module
public import Mathlib
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonEdgeColouring_Solution
public import Theorems.Thm_ShannonColouring_shannon_sharp

set_option autoImplicit true
@[expose] public section
public section
open ShannonTheorem
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

theorem ShannonTheorem.shannon_sharp (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c := by sorry
