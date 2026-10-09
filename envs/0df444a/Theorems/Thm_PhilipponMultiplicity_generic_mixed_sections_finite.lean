-- Prove2me | Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_finite
-- name    : PhilipponMultiplicity.generic_mixed_sections_finite
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T22:18:46.608801+00:00
-- url     : https://prove2.me/theorems/6d8acc52-664b-4b76-b3f0-0b3fcfdc33f4
-- title:
--   Generic normalized mixed sections are finite and avoid the boundary
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$. Let $W\subseteq M$ be closed and irreducible, and choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, using the actual quotient Hilbert-polynomial dimension. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$, and choose a list $l$ containing each block $i$ exactly $\alpha_i$ times.
--
--   Let $R=K[T_{j,v}]$ be the polynomial ring of independent cutting coefficients, let $L=\operatorname{Frac}(R)$, and set $P_j=\sum_tT_{j,(l_j,t)}X_{l_j,t}$. For each pivot choice $b$ and subset $S\subseteq M$, write
--   $$
--   J_b(S)=I(S)R[X_v]+(P_j:j<|l|)+(X_{i,b_i}-1:i),\qquad
--   A_b(S)=L[X_v]/J_b(S)L[X_v].
--   $$
--   Here $I(S)$ is the original multihomogeneous vanishing ideal. Then for every pivot choice $b$,
--   $$
--   \dim_L A_b(W)<\infty,\qquad J_b(B)L[X_v]=L[X_v].
--   $$
--   Thus the generic normalized mixed section is finite and misses the prescribed proper boundary. The zero algebra is allowed; individual charts and mixed intersections need not be nonempty. Unused coefficient variables and zero-length cutting lists are retained.
--
--   **Formalization Note.** This is an auxiliary formulation of generic proper mixed intersection and boundary avoidance, not a verbatim source theorem. Those assertions must still be compared with the specified coefficient function field and the actual normalized quotient algebras. Reducedness is not an assumption of this child: the parent obtains it from the already Proved incidence-domain theorem, explicit maps between the two polynomial presentations, and localization of radical ideals. The existing incidence theorem also supplies its dimension computation, which may be reused when proving finiteness here. No additional generic transversality or smoothness claim is required by this statement.
--
--   **Verified generic finiteness reduction (8 October 2026).** Finiteness now follows from the [Proved incidence domain and dimension theorem](https://prove2.me/theorems/2388a22e-9e25-47be-922f-71e426406a44). The explicit quotient comparison transfers domain structure and a dimension bound to the universal normalized algebra. Noether normalization and transcendence degree then prove algebraicity over the coefficient ring whenever the generic quotient is nonzero; the nonzero generic quotient itself ensures coefficient injectivity. Transferring these relations to the coefficient field makes the finite set of ambient generators integral and proves module finiteness. The zero generic quotient is handled separately. Only [boundary avoidance](https://prove2.me/theorems/2a583386-ae38-4861-9997-5124d741f489) remains Open. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, mixed linear sections, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i) and Corollary 4(i), pp.290–291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary coefficient-generic-point formulation of proper mixed intersection and avoidance of a lower-dimensional closed subset. Comparison with the displayed coordinate quotients remains Open. The parent separately proves reducedness from the Proved mixed_incidence_domain_and_dimension theorem and localization, so reducedness is not included as an Open premise.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem generic_mixed_sections_finite
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
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by sorry

end PhilipponMultiplicity
