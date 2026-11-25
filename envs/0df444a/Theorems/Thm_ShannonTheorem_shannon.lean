-- Prove2me | Theorems.Thm_ShannonTheorem_shannon
-- name    : ShannonTheorem.shannon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:06:19.763034+00:00
-- url     : https://prove2.me/theorems/258b400d-9054-4e6e-a0c7-588e57492081
-- title:
--   Shannon Theorem: shannon
-- statement:
--   **Shannon's theorem** (1949): a loopless multigraph of maximum degree at most `Δ` has a
--   proper edge colouring with `⌊3Δ/2⌋` colours.
--
--   Source: https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/Solution.lean#L39-L42
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/Solution.lean#L39-L42

module
public import Mathlib
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonEdgeColouring_Solution
public import Theorems.Thm_ShannonColouring_shannon

set_option autoImplicit true
@[expose] public section
public section
open ShannonTheorem
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

theorem ShannonTheorem.shannon {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c := by sorry
