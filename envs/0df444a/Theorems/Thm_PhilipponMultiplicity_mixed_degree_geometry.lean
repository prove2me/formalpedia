-- Prove2me | Theorems.Thm_PhilipponMultiplicity_mixed_degree_geometry
-- name    : PhilipponMultiplicity.mixed_degree_geometry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:10.42923+00:00
-- url     : https://prove2.me/theorems/717d6098-89fa-4e68-a661-6911c16fbc91
-- title:
--   Sections 2–3 — geometric meaning of mixed degree
-- statement:
--   For an irreducible locally closed subvariety $V$ of a product of projective spaces and an admissible mixed index $\alpha$ of total degree $\dim V$, the normalized mixed Hilbert coefficient is the maximum cardinality of a finite intersection with linear subspaces of codimensions $\alpha_i$.
--
--   An accepted proof-sketch establishes the finite-set Hilbert polynomial by homogeneous interpolation and reduces the locally closed case to two geometric inputs: the [isolated-section degree bound](p2m:theorem/e89193b3-ac48-4227-b11f-598b761ffed3) and a [general section avoiding the closed boundary](p2m:theorem/db460d95-700e-4a5c-8c39-f5a6261c5849). Both inputs remain Open. The reduction permits positive-dimensional components of a special section on the boundary and proves the finite-point cardinality conversion, including the empty set.
--
--   Source: [Philippon (1986), pp. 359 and 364](https://numdam.org/articles/10.24033/bsmf.2060/). The formal statement and mixed-coefficient normalization are unchanged.
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
