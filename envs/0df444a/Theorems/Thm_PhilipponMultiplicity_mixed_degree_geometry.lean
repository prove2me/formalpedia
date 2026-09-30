-- Prove2me | Theorems.Thm_PhilipponMultiplicity_mixed_degree_geometry
-- name    : PhilipponMultiplicity.mixed_degree_geometry
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T21:11:10.42923+00:00
-- url     : https://prove2.me/theorems/717d6098-89fa-4e68-a661-6911c16fbc91
-- title:
--   Sections 2–3 — geometric meaning of mixed degree
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   For an irreducible locally closed subvariety and an admissible mixed index, the actual mixed Hilbert coefficient is the maximum number of points in a finite intersection with linear subspaces of the specified codimensions.
-- source:
--   1986, pp.359,364. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree

theorem mixed_degree_geometry
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K) (V : Set M.Point)
    (hV : @IsLocallyClosed _ M.zariskiTopology V)
    (hirr : @IsIrreducible _ M.zariskiTopology V)
    (α : M.FactorIndex → ℕ) (hα : ∀ i, α i ≤ M.ambientDimension i)
    (hsum : ∑ i, α i = locusDimension M V) :
    (∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      (linearSlice M V L).Finite →
      ((linearSlice M V L).ncard : ℚ) ≤ idealMixedDegree M (M.vanishingIdeal V) α) ∧
    (∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
      (linearSlice M V L).Finite ∧
      ((linearSlice M V L).ncard : ℚ) = idealMixedDegree M (M.vanishingIdeal V) α) := by sorry

end PhilipponMultiplicity
