-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_coordinate_local_mixed_section_preserving_isolated_points
-- name    : PhilipponMultiplicity.exists_coordinate_local_mixed_section_preserving_isolated_points
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T17:40:50.447015+00:00
-- url     : https://prove2.me/theorems/33592a31-6a4e-4aa2-bc8f-26dbfd4c2c94
-- title:
--   Coordinate-local mixed sections preserving isolated point counts
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible variety. Fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$. Let $L_i\subseteq K^{N_i+1}$ have dimension $N_i+1-\alpha_i$, and let $S$ be a finite subset of the section $Z=W\cap\prod_i\mathbf P(L_i)$. Assume that each $x\in S$ has a Zariski-open neighborhood $U$ with $U\cap Z\subseteq S$.
--
--   There are subspaces $L'_i$ of the same dimensions such that $Z'=W\cap\prod_i\mathbf P(L'_i)$ is finite, together with an injection of sets $S\hookrightarrow Z'$. There are also an ordered list of blocks $i_0,\ldots,i_{n-1}$, block-linear forms $P_k$, and actual cut ideals $J_k\subseteq R=K[X_{ij}]$ such that
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   On $W$, the equations $P_k=0$ for $k<n$ define exactly $Z'$.
--
--   For every choice of one coordinate $j_i$ in each block, put $s_j=\prod_i X_{i,j_i}$ and $R_j=R[1/s_j]$. At each step $k<n$, multiplication by $P_k$ is injective on $R_j/J_kR_j$. The final quotient $R_j/J_nR_j$ is reduced. These conditions hold on every member of this finite coordinate cover of the relevant multicone.
--
--   The special section $Z$ may have positive-dimensional components away from $S$. The injection need not be a geometric morphism and does not assert that the original points lie in $Z'$. Empty sections, empty cutting lists, and zero localized quotients are allowed.
--
--   **Formalization Note.** This is an auxiliary synthesis of isolated-point persistence, general reduced sections, and generic filter regularity. Constructing the section, injection, and flag simultaneously in the stated coordinates remains Open. The principal localizations are rings of opens of the multicone, not degree-zero dehomogenized charts. No eventual homogeneous ideal equality, Hilbert function assertion, mixed coefficient, numerical degree bound, or primary-prime avoidance is assumed.
--
--
--   **Verified reduction to geometric points.** The accepted sketch applies the checked Jacobson-ring membership criterion on principal opens to propagate injectivity and radicality from maximal localizations. The weak Nullstellensatz identifies the required maximal ideals with evaluation ideals of vectors whose blocks are nonzero. Points outside a cut have the unit localized ideal, so conditions are needed only on its actual geometric points. The reduction preserves the same injection of the prescribed isolated point set into the new finite section.
--
--   The sole Open dependency is [point-local sections preserving isolated points](https://prove2.me/theorems/86af3766-9a7c-446d-9194-780a3a5fdefe). It supplies the same section, injection, and flag, with injectivity at geometric points of each successive cut and reducedness at geometric points of the final cut. No property of an entire coordinate localization is assumed there. Simultaneous geometric choice and isolated-point persistence remain Open; the passage from the point-local conditions to the displayed coordinate-open conditions is proved.
-- source:
--   Philippon (1986), pp. 363–364, the exact-sequence proof of Lemma 3.1 and the following paragraph computing mixed coefficients by general sections, https://numdam.org/articles/10.24033/bsmf.2060/ . Persistence: William Fulton, Intersection Theory, 2nd ed. (1998), Section 10.2, Theorem 10.2 and Example 10.2.1, pp. 181–182; see also Corollary 13.1(b), pp. 236–237, for isolated points and positivity in a variety with globally generated tangent bundle (as for a product of projective spaces), https://doi.org/10.1007/978-1-4612-1700-8 ; text consulted at https://djvu.online/file/Pl4avuZzLcI6I . Reduced general sections: S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Filter regularity: Nguyen Tien Manh and Duong Quoc Viet, arXiv:0901.3825v1, Definition 2.1, Proposition 2.4 and Proposition 2.6, pp. 3, 5, 6, https://arxiv.org/abs/0901.3825 . Auxiliary combined formulation; the simultaneous generic choice with point persistence remains to be formalized. In this coordinate-local variant, regularity means injectivity on each R[1/s_j]/J_kR[1/s_j], and final reducedness means radicality of the localized final ideal. The scheme-to-coordinate-ring translation and simultaneous choice preserving the isolated-point count are included in the Open geometric assertion. The algebraic passage to eventual homogeneous conditions is proved separately.

import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree

theorem exists_coordinate_local_mixed_section_preserving_isolated_points
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
      ∃ L' : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L' i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L').Finite ∧
        Nonempty (S ↪ linearSlice M W L') ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let f := algebraMap M.CoordinateRing
                (Localization.Away (∏ i,
                  (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L' ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.Away (∏ i,
                (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical) := by sorry

end PhilipponMultiplicity
