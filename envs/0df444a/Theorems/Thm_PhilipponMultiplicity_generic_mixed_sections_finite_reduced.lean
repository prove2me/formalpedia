-- Prove2me | Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_finite_reduced
-- name    : PhilipponMultiplicity.generic_mixed_sections_finite_reduced
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T21:58:31.959991+00:00
-- url     : https://prove2.me/theorems/aba5e8e9-296e-4a44-bc4a-2c277c8e3f09
-- title:
--   Generic normalized mixed sections are finite and reduced and avoid the boundary
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$. Let $W\subseteq M$ be closed and irreducible, and let $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, using the actual quotient Hilbert-polynomial dimension. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$. Choose a list $l$ containing each block $i$ exactly $\alpha_i$ times.
--
--   Set $R=K[T_{j,v}]$, $L=\operatorname{Frac}(R)$, and $P_j=\sum_tT_{j,(l_j,t)}X_{l_j,t}$. For a pivot choice $b$ and a subset $S\subseteq M$, define
--   $$
--   J_b(S)=I(S)R[X_v]+(P_j:j<|l|)+(X_{i,b_i}-1:i),\qquad
--   A_b(S)=L[X_v]/J_b(S)L[X_v].
--   $$
--   Here $I(S)$ is the original multihomogeneous vanishing ideal. For every pivot choice $b$, the actual generic normalized coordinate algebra $A_b(W)$ is finite-dimensional over $L$ and reduced, and
--   $$
--   J_b(B)L[X_v]=L[X_v].
--   $$
--   The zero algebra is allowed; no nonemptiness is asserted for an individual chart or mixed intersection. Unused coefficient variables and zero-length cutting lists are retained.
--
--   **Formalization Note.** This is an auxiliary geometric statement at the coefficient generic point, motivated by generic proper and transverse mixed linear sections. Its identification with the displayed concrete polynomial quotients, including the Hilbert-polynomial dimension comparison and avoidance of both the singular locus and the proper boundary, remains Open. Reducedness concerns the coordinate algebra itself, including possible nilpotents, rather than just its set of field-valued points. The parent proof now constructs the Jacobian certificate from coordinate minimal polynomials and proves that the Jacobian obstruction ideal commutes with coefficient localization. Neither Jacobian certificates nor principal-open specialization conclusions are assumptions of this child.
--
--   **Verified reducedness reduction (8 October 2026).** Reducedness now follows from the [Proved mixed-incidence domain theorem](https://prove2.me/theorems/2388a22e-9e25-47be-922f-71e426406a44). Explicit polynomial maps compare its presentation at $H=1$ with the universal normalized ideal here, giving an injection of quotient rings. Localization at nonzero coefficient polynomials then preserves reducedness. Both the zero-chart and zero-generic-fibre cases are included, without a dominance assumption. The only remaining Open input is [generic finiteness and boundary avoidance](https://prove2.me/theorems/6d8acc52-664b-4b76-b3f0-0b3fcfdc33f4); it has no reducedness or transversality premise. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, mixed linear sections, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2 and Corollary 4, pp.290–291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary generic-fibre formulation, not a verbatim source theorem. Generic proper and transverse intersection, singular-locus and boundary avoidance, and comparison with these actual normalized quotients remain Open. The parent proves the finite-reduced-algebra Jacobian certificate and its descent to the universal coefficient ring by clearing scalar denominators.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem generic_mixed_sections_finite_reduced
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          Module.Finite (FractionRing (GenericMixedSections.CoeffRing M l))
            (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          IsReduced (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by sorry

end PhilipponMultiplicity
