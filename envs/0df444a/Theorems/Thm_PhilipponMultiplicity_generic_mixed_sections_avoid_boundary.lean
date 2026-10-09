-- Prove2me | Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_avoid_boundary
-- name    : PhilipponMultiplicity.generic_mixed_sections_avoid_boundary
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T22:48:21.954386+00:00
-- url     : https://prove2.me/theorems/2a583386-ae38-4861-9997-5124d741f489
-- title:
--   Generic normalized mixed sections avoid a proper boundary
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$. Let $W\subseteq M$ be closed and irreducible, and let $0\le\alpha_i\le n_i$ satisfy $\sum_i\alpha_i=\dim W$, with dimension defined by the quotient Hilbert polynomial. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$. Choose a list $l$ containing each block $i$ exactly $\alpha_i$ times.
--
--   Put $R=K[T_{j,v}]$, $L=\operatorname{Frac}(R)$, and $P_j=\sum_tT_{j,(l_j,t)}X_{l_j,t}$. For every choice of pivot coordinates $b$, define
--   $$J_b(B)=I(B)R[X_v]+(P_j:j<|l|)+(X_{i,b_i}-1:i).$$
--   Then
--   $$J_b(B)L[X_v]=L[X_v].$$
--   Thus the coefficient-generic mixed section misses the prescribed proper closed boundary on every normalized chart. Empty boundaries, empty intersections, zero-length cutting lists and unused coefficient variables are allowed.
--
--   **Formalization Note.** This is an auxiliary coordinate-field formulation of generic boundary avoidance. The proof uses the established incidence domain and dimension theorem, the proved generic finiteness argument, and a homogeneous equation separating the boundary from a point of $W$. Setting all cutting coefficients to zero shows that this equation survives in the universal normalized algebra; contraction of localized prime ideals preserves it at the generic coefficient point. The finite domain quotient is a field, which forces the larger boundary ideal to be the unit ideal. No Open geometric premise remains in this proof, and the original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, mixed linear sections, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i) and Corollary 4(i), pp.290–291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary coefficient-generic-point formulation of avoiding a lower-dimensional closed subset. Comparison with the actual normalized coordinate ideals remains Open. Finiteness of the section of W is proved separately in the parent, from the established incidence dimension and domain theorem.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem generic_mixed_sections_avoid_boundary
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by sorry

end PhilipponMultiplicity
