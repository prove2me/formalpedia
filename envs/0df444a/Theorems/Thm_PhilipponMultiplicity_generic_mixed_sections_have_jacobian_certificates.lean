-- Prove2me | Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_have_jacobian_certificates
-- name    : PhilipponMultiplicity.generic_mixed_sections_have_jacobian_certificates
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T21:38:33.662305+00:00
-- url     : https://prove2.me/theorems/deaa405c-4743-4640-ae51-825bea6097ef
-- title:
--   Generic mixed sections have Jacobian and boundary unit-ideal certificates
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the actual quotient Hilbert polynomial. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$. Let $l$ be an ordered list containing each block $i$ exactly $\alpha_i$ times.
--
--   Write $R=K[T_{j,v}]$ for the polynomial ring in independent entries of the cutting coefficient array, $L=\operatorname{Frac}(R)$, and $A=R[X_v]$ for the ambient coordinate polynomial ring. Its universal cutting rows are
--   $$
--   P_j=\sum_{t=0}^{n_{l_j}}T_{j,(l_j,t)}X_{l_j,t}.
--   $$
--   For a set $S\subseteq M$ and a pivot choice $b_i\in\{0,\ldots,n_i\}$, put
--   $$
--   J_b(S)=I(S)A+(P_j:j<|l|)+(X_{i,b_i}-1:i).
--   $$
--   Here $I(S)$ is the original homogeneous vanishing ideal, extended from $K[X_v]$ to $A$. If $N=\sum_i(n_i+1)$, define the Jacobian obstruction ideal
--   $$
--   \mathcal J(J)=J+\left(\det\!\left(\frac{\partial Q_u}{\partial X_v}\right)_{u,v}:Q_1,\ldots,Q_N\in J\right).
--   $$
--   All derivatives are in ambient coordinates, treating the coefficient variables as constants. Then for every pivot choice $b$,
--   $$
--   \mathcal J(J_b(W))\,L[X_v]=L[X_v],\qquad
--   J_b(B)\,L[X_v]=L[X_v].
--   $$
--   These are unit-ideal certificates for absence of a Jacobian obstruction and of a boundary intersection over the coefficient function field. They do not assert the existence of a principal open subset of coefficient arrays; the parent reduction constructs that subset by clearing denominators simultaneously for all charts. Empty charts and zero-length cutting lists are included.
--
--   **Formalization Note.** This is an auxiliary generic-fibre formulation motivated by the cited transversality results, not their verbatim statement. Generic proper intersection, transversality away from the singular locus, boundary avoidance, the Hilbert-polynomial dimension comparison, and identification with these actual normalized ideals remain Open. The Jacobian ideal is formed from tuples in the universal ideal before extending coefficients to $L$; passage from a generic cotangent-space calculation to this certificate is part of the remaining comparison. The parent reduction handles denominator clearing, coefficient specialization, and recovery of the exact pointwise projective conclusion.
--
--   **Verified finite reduced generic-fibre reduction (8 October 2026).** It suffices to prove that the [actual generic normalized mixed-section quotients are finite-dimensional and reduced and avoid the boundary](https://prove2.me/theorems/aba5e8e9-296e-4a44-bc4a-2c277c8e3f09). Coordinate minimal polynomials over a perfect field give a diagonal Jacobian with determinant invertible modulo the ideal. Clearing scalar denominators then proves that the full Jacobian obstruction ideal commutes with coefficient localization, yielding the exact universal certificate in this theorem. The generic geometric claims remain Open, including comparison with the actual normalized coordinate rings; the cotangent-to-Jacobian and universal/localized-ideal conversions are no longer additional assumptions. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2 and Corollary 4, pp.290–291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Stacks Project, Lemmas 10.131.9 and 10.131.14, https://stacks.math.columbia.edu/tag/00RM , for the conormal presentation and coordinate differentials. Auxiliary synthesis at the coefficient generic point: proper transverse intersection on the smooth locus, avoidance of the singular locus and proper boundary, and conversion to the displayed universal Jacobian and boundary ideals. The concrete geometric comparisons remain Open. The parent separately proves denominator clearing and specialization to a principal open.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem generic_mixed_sections_have_jacobian_certificates
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.jacobianIdeal
            (GenericMixedSections.normalizedIdeal M l W b)).map
              (GenericMixedSections.genericMap M l) = ⊤ ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by sorry

end PhilipponMultiplicity
