-- Prove2me | Theorems.Thm_PhilipponMultiplicity_isolated_mixed_linear_section_bound
-- name    : PhilipponMultiplicity.isolated_mixed_linear_section_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T13:19:58.044992+00:00
-- url     : https://prove2.me/theorems/e89193b3-ac48-4227-b11f-598b761ffed3
-- title:
--   Mixed-degree bound for isolated points of a linear section
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{N_i}$. Let $W\subseteq M$ be closed and irreducible, let $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$, and let $L_i$ have codimensions $\alpha_i$. If $S\subseteq W\cap\prod_iL_i$ is finite and locally isolated in that section, then
--   $$
--   \mathcal H(S;1,\ldots,1)\le c_\alpha(I(W)).
--   $$
--   Local isolation means that each $x\in S$ has a Zariski-open neighborhood $U$ with $U\cap W\cap\prod_iL_i\subseteq S$. Other components of the section may have positive dimension. Both sides use the actual multigraded quotient Hilbert polynomial and its established factorial normalization.
--
--   An accepted proof-sketch reduces this bound to [a reduced filter-regular section preserving the isolated point count](p2m:theorem/f2bb6eb4-f901-41b5-8932-79d7d68d38b3). The checked algebra computes the section's mixed degree by iterated finite differences, identifies the degree of each finite point set with its cardinality, and applies the injection supplied by the geometric lemma. Constructing that section and injection remains Open; the numerical bound is therefore not yet proved.
--
--   Source: [Philippon (1986), pp. 359, 363–364 and the isolated-component argument of Proposition 3.3, pp. 365–370](https://numdam.org/articles/10.24033/bsmf.2060/). This is an auxiliary formulation of the isolated-intersection bound. The formal statement has not changed.
-- source:
--   Philippon (1986), pp. 359 and 364, geometric interpretation of the mixed degrees, and the isolated-component intersection argument of Proposition 3.3, pp. 365–370. https://numdam.org/articles/10.24033/bsmf.2060/ . Auxiliary formulation for a finite locally isolated subset of a possibly improper linear section; the bound remains Open.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree

theorem isolated_mixed_linear_section_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      locusDegreeValue M S (fun _ => 1) ≤ idealMixedDegree M (M.vanishingIdeal W) α := by sorry

end PhilipponMultiplicity
