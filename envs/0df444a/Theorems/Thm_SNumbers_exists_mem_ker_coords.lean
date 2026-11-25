-- Prove2me | Theorems.Thm_SNumbers_exists_mem_ker_coords
-- name    : SNumbers.exists_mem_ker_coords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:27.868085+00:00
-- url     : https://prove2.me/theorems/2e5cb895-c0ac-4673-a52d-4a334deaaf85
-- title:
--   SNumbers: exists mem ker coords
-- statement:
--   **Coordinate pigeonhole.** A subspace `V ⊆ 𝕜^m` whose dimension exceeds the
--   size of a coordinate set `A` contains a nonzero vector vanishing on `A`. The
--   restriction `V → (A → 𝕜)` has range of dimension `≤ |A| < dim V`, so a nonzero
--   kernel by rank–nullity.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L77-L91
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L77-L91

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SNumbers.exists_mem_ker_coords {V : Submodule 𝕜 (Fin m → 𝕜)}
    {A : Finset (Fin m)} (hA : A.card < Module.finrank 𝕜 V) :
    ∃ y ∈ V, y ≠ 0 ∧ ∀ i ∈ A, y i = 0 := by sorry
