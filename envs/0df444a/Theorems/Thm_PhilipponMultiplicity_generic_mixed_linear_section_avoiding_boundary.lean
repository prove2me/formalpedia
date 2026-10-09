-- Prove2me | Theorems.Thm_PhilipponMultiplicity_generic_mixed_linear_section_avoiding_boundary
-- name    : PhilipponMultiplicity.generic_mixed_linear_section_avoiding_boundary
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T13:24:36.422284+00:00
-- url     : https://prove2.me/theorems/db460d95-700e-4a5c-8c39-f5a6261c5849
-- title:
--   General mixed linear section avoiding a proper closed boundary
-- statement:
--   Let $W$ be a closed irreducible subvariety of a product of projective spaces over a Philippon base field, and let $B\subset W$ be a proper closed subset. For an admissible mixed index $\alpha$ with $\sum_i\alpha_i=\dim W$, there is a finite intersection $Z=W\cap\prod_iL_i$, where $L_i$ has codimension $\alpha_i$, such that $Z\cap B=\varnothing$ and
--   $$
--   \mathcal H(Z;1,\ldots,1)=c_\alpha(I(W)).
--   $$
--
--   An accepted proof-sketch proves the Hilbert-polynomial computation and reduces the theorem to the [existence of a filter-regular mixed linear flag with reduced final ideal](p2m:theorem/9cb97862-bbc3-49d4-bd20-d0aa77d62e44). That geometric child remains Open. The checked algebra identifies Hilbert polynomials from eventual homogeneous-piece equality, applies the colon exact sequence to each cut, and proves that iterated mixed finite differences extract the top coefficient with the exact product-of-factorials normalization. Zero coefficients and empty final sections are allowed.
--
--   Source: [Philippon (1986), pp. 363–364](https://numdam.org/articles/10.24033/bsmf.2060/), Lemma 3.1 and the general-section interpretation before Lemma 3.2. The formal statement is unchanged.
-- source:
--   Philippon (1986), p. 364, the paragraph preceding Lemma 3.2: computation of the mixed Hilbert coefficient by general linear subspaces; see also the mixed-degree definition on p. 359. https://numdam.org/articles/10.24033/bsmf.2060/ . The proper-closed-boundary avoidance is the explicit genericity refinement needed for the mission’s locally closed formulation and remains Open.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree

theorem generic_mixed_linear_section_avoiding_boundary
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        locusDegreeValue M (linearSlice M W L) (fun _ => 1) =
          idealMixedDegree M (M.vanishingIdeal W) α := by sorry

end PhilipponMultiplicity
