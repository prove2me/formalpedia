-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_point_local_mixed_section_preserving_isolated_points
-- name    : PhilipponMultiplicity.exists_point_local_mixed_section_preserving_isolated_points
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T20:42:09.530378+00:00
-- url     : https://prove2.me/theorems/86af3766-9a7c-446d-9194-780a3a5fdefe
-- title:
--   Point-local regular sections preserving isolated point counts
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible variety. Fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$. Let $L_i\subseteq K^{N_i+1}$ have dimension $N_i+1-\alpha_i$, and let $S$ be a finite subset of the section $Z=W\cap\prod_i\mathbf P(L_i)$. Assume that each $x\in S$ has a Zariski-open neighborhood $U$ with $U\cap Z\subseteq S$.
--
--   There are subspaces $L'_i$ of the same dimensions such that $Z'=W\cap\prod_i\mathbf P(L'_i)$ is finite, together with an injection of sets $S\hookrightarrow Z'$. There are also an ordered list of blocks $i_0,\ldots,i_{n-1}$, block-linear forms $P_k$, and actual cut ideals $J_k\subseteq R=K[X_{ij}]$ satisfying
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   On $W$, the equations $P_k=0$ for $k<n$ define exactly $Z'$.
--
--   For a vector $v=(v_{ij})$ whose every block is nonzero, let $\mathfrak m_v=\{Q\in R:Q(v)=0\}$. The same flag satisfies the following conditions at actual geometric points of its successive multicones:
--
--   1. For every $k<n$ and every such $v$ with $Q(v)=0$ for all $Q\in J_k$, multiplication by $P_k$ is injective on $R_{\mathfrak m_v}/J_kR_{\mathfrak m_v}$.
--   2. For every such $v$ with $Q(v)=0$ for all $Q\in J_n$, the quotient $R_{\mathfrak m_v}/J_nR_{\mathfrak m_v}$ is reduced.
--
--   The special section $Z$ may have positive-dimensional components away from $S$. The injection need not be a geometric morphism and does not assert that the original points lie in $Z'$. Empty sections, empty cutting lists, and zero local quotients are allowed.
--
--   **Formalization Note.** These are local rings of the multicone at evaluation maximal ideals, retaining the affine scale in each projective block. Conditions are imposed only at points lying on the corresponding cut, and vectors with a zero block are excluded. A checked proof-sketch reduces the simultaneous choice to [isolated-point count persistence on a principal open](https://prove2.me/theorems/2a246e47-34c6-4f2c-a0fb-a5aa936f6df2) and the existing [principal-open smooth mixed-flag family](https://prove2.me/theorems/cb087b60-bd87-46f8-8672-81234ffb113d). These two geometric inputs remain Open. The simultaneous coefficient selection, associated-prime local injectivity, and smooth-to-radical local algebra are proved in the reduction. This auxiliary synthesis of isolated-point persistence, generic filter regularity, and reduced general sections is not a verbatim theorem from one source. No condition on an entire coordinate localization, no eventual homogeneous ideal condition, and no numerical mixed-degree count is assumed.
-- source:
--   Philippon (1986), pp. 363–364, the exact-sequence proof of Lemma 3.1 and the following paragraph computing mixed coefficients by general sections, https://numdam.org/articles/10.24033/bsmf.2060/ . Persistence: William Fulton, Intersection Theory, 2nd ed. (1998), Section 10.2, Theorem 10.2 and Example 10.2.1, pp. 181–182; see also Corollary 13.1(b), pp. 236–237, for isolated points and positivity in a variety with globally generated tangent bundle (as for a product of projective spaces), https://doi.org/10.1007/978-1-4612-1700-8 ; text consulted at https://djvu.online/file/Pl4avuZzLcI6I . Reduced general sections: S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Filter regularity: Nguyen Tien Manh and Duong Quoc Viet, arXiv:0901.3825v1, Definition 2.1, Proposition 2.4 and Proposition 2.6, pp. 3, 5, 6, https://arxiv.org/abs/0901.3825 . Auxiliary combined formulation; the simultaneous generic choice with point persistence remains to be formalized. Point-local variant: injectivity is required only at the evaluation maximal ideals of the successive cuts with nonzero coordinate blocks, and reducedness only at such points of the final cut. The injection of isolated point sets is retained. The simultaneous geometric choice, isolated-point persistence, and passage from transversality to these concrete local rings remain Open. The separate checked reduction reuses the Jacobson property and the weak Nullstellensatz to obtain the coordinate-open conclusions.

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_point_local_mixed_section_preserving_isolated_points
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
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let f := algebraMap M.CoordinateRing
                (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L' ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by sorry

end PhilipponMultiplicity
