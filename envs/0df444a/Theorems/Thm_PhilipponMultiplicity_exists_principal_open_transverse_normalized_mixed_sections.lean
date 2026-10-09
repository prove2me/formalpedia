-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_transverse_normalized_mixed_sections
-- name    : PhilipponMultiplicity.exists_principal_open_transverse_normalized_mixed_sections
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T21:03:24.816986+00:00
-- url     : https://prove2.me/theorems/a9b9ed86-6b3e-443d-9c74-a648242f5ae1
-- title:
--   Generic normalized mixed sections have full-rank pointwise Jacobians
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the actual quotient Hilbert polynomial. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$. Let $l$ be an ordered list containing each block $i$ exactly $\alpha_i$ times.
--
--   For a coefficient array $c$, write $P_j(c)$ for its block-linear cutting rows, $I(c)=I(W)+(P_j(c):j<|l|)$, and $Z(c)$ for their common zero set in $W$. There exists a nonzero polynomial $F$ in the coefficient entries such that $F(c)\ne0$ implies $Z(c)\cap B=\varnothing$ and the following pointwise Jacobian condition. For every pivot choice $b_i\in\{0,\ldots,n_i\}$, put
--   $$
--   J_b(c)=I(c)+(X_{i,b_i}-1:i).
--   $$
--   At every common zero $a\in K^N$ of this ideal, where $N=\sum_i(n_i+1)$, there exist $N$ polynomials $Q_1,\ldots,Q_N\in J_b(c)$ such that
--   $$
--   \det\!\left(\frac{\partial Q_u}{\partial X_v}(a)\right)_{u,v}\ne0.
--   $$
--   Equivalently, their gradients form a basis of $K^N$. The equations may depend on the chart, coefficients, and point; they need not generate the ideal. All variables, including the normalized pivots, occur in this square Jacobian. Empty charts and zero-length cutting lists are allowed.
--
--   **Formalization Note.** This is an auxiliary affine formulation of generic transverse mixed sections, motivated by the cited geometric results, not a verbatim statement. The unproved work includes avoiding the singular locus and prescribed boundary, generic transversality, the Hilbert-polynomial dimension comparison, the relation between the concrete normalized ideals and projective intersections, and a nonzero principal-open condition in coefficient space. Neither finiteness nor radicality is assumed here: the parent reduction proves both from the displayed pointwise condition. Coefficients outside a row's selected block remain unused.
--
--   **Verified generic-fibre reduction (8 October 2026).** It suffices to establish [Jacobian and boundary unit-ideal certificates over the coefficient function field](https://prove2.me/theorems/deaa405c-4743-4640-ae51-825bea6097ef). The new proof clears denominators in a finite family of generic unit ideals and multiplies the resulting nonzero coefficients to obtain one principal-open condition. It verifies specialization of the universal cutting rows and Jacobian determinants, derives full rank at every common zero, and proves boundary avoidance by normalizing projective representatives. The new child contains no principal-open assumption. Generic transversality and its concrete coefficient-field and normalized-ideal comparisons remain Open; the original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2 and Corollary 4, pp.290–291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis: apply generic proper transverse intersection to the smooth locus of W and products of projective linear subspaces in characteristic zero; avoid the lower-dimensional singular locus and prescribed proper boundary; pull back to coefficient space and a nonzero principal open; express the zero tangent-space condition using equations of each actual normalized ideal. These adaptations remain Open. The parent proves the pointwise Jacobian criterion for radicality and finiteness, and the chart-to-projective finiteness transfer.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_transverse_normalized_mixed_sections
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let J := MixedFlag.ideal M (M.vanishingIdeal W) l c l.length ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
              ∀ a : M.Variable → K, (∀ P ∈ J, MvPolynomial.eval a P = 0) →
                ∃ Q : M.Variable → M.CoordinateRing, (∀ i, Q i ∈ J) ∧
                  MvPolynomial.eval a
                    (Matrix.of (fun i j => MvPolynomial.pderiv j (Q i))).det ≠ 0) := by sorry

end PhilipponMultiplicity
