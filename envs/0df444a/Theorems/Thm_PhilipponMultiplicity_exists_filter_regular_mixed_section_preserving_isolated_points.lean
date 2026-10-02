-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_filter_regular_mixed_section_preserving_isolated_points
-- name    : PhilipponMultiplicity.exists_filter_regular_mixed_section_preserving_isolated_points
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T15:31:17.481409+00:00
-- url     : https://prove2.me/theorems/f2bb6eb4-f901-41b5-8932-79d7d68d38b3
-- title:
--   Reduced filter-regular sections preserving isolated point counts
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible variety. Fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$. Let $L_i$ be linear subspaces of codimensions $\alpha_i$, and let $S\subseteq W\cap\prod_iL_i$ be finite and locally isolated: each point $x\in S$ has a Zariski-open neighborhood $U$ with
--   $$
--   U\cap W\cap\prod_iL_i\subseteq S.
--   $$
--   There exist linear subspaces $L'_i$ of the same codimensions such that $Z'=W\cap\prod_iL'_i$ is finite, together with an injection of sets $S\hookrightarrow Z'$.
--
--   The section $Z'$ can be accompanied by block indices $i_0,\ldots,i_{n-1}$, block-linear equations $P_k$, and cut ideals $J_k$ with
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\quad J_0=I(W),\quad
--   \deg P_k=e_{i_k},\quad J_{k+1}=J_k+(P_k).
--   $$
--   Each multiplication by $P_k$ is injective in all sufficiently large homogeneous quotient pieces:
--   $$
--   P_kQ\in J_k\ \Longrightarrow\ Q\in J_k
--   \qquad(Q\in R_D,\ D\gg0).
--   $$
--   The final ideal has the reduced section's homogeneous pieces in all sufficiently large block degrees:
--   $$
--   (J_n)_D=I(Z')_D\qquad(D\gg0).
--   $$
--   The thresholds may depend on the stage. No mixed Hilbert coefficient or degree inequality is assumed. The original section may have additional components of positive dimension; only the chosen finite set is locally isolated. The empty set and zero-length flag are allowed.
--
--   **Formalization Note.** This combines persistence of isolated intersection points with a general reduced filter-regular section. It is an auxiliary consequence of the cited intersection and generic-section results, not a verbatim theorem from one source. The injection is an injection of finite point sets, not an asserted geometric morphism or literal inclusion of the original points. Constructing the section, injection, and flag simultaneously remains Open.
--
--
--   **Verified coordinate-local reduction.** The accepted sketch proves that a uniform sufficiently-large-degree bound makes homogeneous membership detectable on the finitely many coordinate principal opens of the multicone. Local injectivity therefore implies the displayed eventual injectivity. It also proves a coordinate-local Nullstellensatz: if the final cut is reduced on those opens, its localized ideal equals the geometric vanishing ideal of its zero set. This yields the displayed eventual homogeneous equality.
--
--   The only Open dependency is [coordinate-local mixed sections preserving isolated point counts](https://prove2.me/theorems/33592a31-6a4e-4aa2-bc8f-26dbfd4c2c94). It supplies the geometric section, equations, injection, localized injectivity, and final localized reducedness. It assumes no eventual homogeneous assertion or numerical mixed-degree bound. The original isolated points and their injection are preserved by the reduction. The simultaneous geometric construction and persistence remain Open.
-- source:
--   Philippon (1986), pp. 363–364, the exact-sequence proof of Lemma 3.1 and the following paragraph computing mixed coefficients by general sections, https://numdam.org/articles/10.24033/bsmf.2060/ . Persistence: William Fulton, Intersection Theory, 2nd ed. (1998), Section 10.2, Theorem 10.2 and Example 10.2.1, pp. 181–182; see also Corollary 13.1(b), pp. 236–237, for isolated points and positivity in a variety with globally generated tangent bundle (as for a product of projective spaces), https://doi.org/10.1007/978-1-4612-1700-8 ; text consulted at https://djvu.online/file/Pl4avuZzLcI6I . Reduced general sections: S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Filter regularity: Nguyen Tien Manh and Duong Quoc Viet, arXiv:0901.3825v1, Definition 2.1, Proposition 2.4 and Proposition 2.6, pp. 3, 5, 6, https://arxiv.org/abs/0901.3825 . Auxiliary combined formulation; the simultaneous generic choice with point persistence remains to be formalized.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree

theorem exists_filter_regular_mixed_section_preserving_isolated_points
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
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L'))) := by sorry

end PhilipponMultiplicity
