-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_point_local_conditions
-- name    : PhilipponMultiplicity.exists_mixed_cut_flag_with_point_local_conditions
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T20:01:51.004981+00:00
-- url     : https://prove2.me/theorems/2f19ff63-31f1-4714-a5cb-c46ac7c7fc78
-- title:
--   Mixed cut flags with regular cuts and reducedness at geometric points
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible subvariety. Let $B\subsetneq W$ be closed, and fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$.
--
--   There are vector subspaces $L_i\subseteq K^{N_i+1}$ with $\dim L_i+\alpha_i=N_i+1$ such that $Z=W\cap\prod_i\mathbf P(L_i)$ is finite and disjoint from $B$. There are an ordered list of blocks $i_0,\ldots,i_{n-1}$, block-linear forms $P_k$, and actual cut ideals $J_k\subseteq R=K[X_{ij}]$ satisfying
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   On $W$, the equations $P_k=0$ for $k<n$ define exactly $Z$.
--
--   For a vector $v=(v_{ij})$ whose every block is nonzero, let $\mathfrak m_v=\{Q\in R:Q(v)=0\}$. The same flag satisfies the following conditions at actual geometric points of its successive multicones:
--
--   1. For every $k<n$ and every such $v$ with $Q(v)=0$ for all $Q\in J_k$, multiplication by $P_k$ is injective on $R_{\mathfrak m_v}/J_kR_{\mathfrak m_v}$.
--   2. For every such $v$ with $Q(v)=0$ for all $Q\in J_n$, the quotient $R_{\mathfrak m_v}/J_nR_{\mathfrak m_v}$ is reduced.
--
--   **Formalization Note.** An accepted sketch reduces this assertion to [the existence of a flag with completed local conditions](https://prove2.me/theorems/2a7402c2-8ec5-4373-b8a0-be546465fac7). Descent of multiplication injectivity and radicality from the maximal-ideal completion is proved using faithful flatness. The simultaneous geometric flag construction and identification of the completed local equations remain Open. The local rings are those of the ambient multicone at evaluation maximal ideals, restricted to nonzero coordinate blocks and actual cut points; empty final sections are permitted.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bulletin de la SMF 114 (1986), Lemma 3.1 and the following mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1, p. 3, notes (i)–(ii), p. 4, and Proposition 2.6, p. 6, https://arxiv.org/abs/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, and Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Auxiliary synthesis: a sufficiently general flag is filter-regular on each coordinate localization; transversality on the smooth open of W gives a reduced final section avoiding B and the singular complement. The simultaneous choice and bridge to the displayed multicone localization conditions remain Open. Point-local variant: injectivity is required only at the evaluation maximal ideals of the successive cuts with nonzero coordinate blocks, and reducedness only at such points of the final cut. The simultaneous geometric choice and passage from transversality to these concrete local rings remain Open. The separate checked reduction uses the Jacobson property and the weak Nullstellensatz to obtain the coordinate-open conclusions.

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_mixed_cut_flag_with_point_local_conditions
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
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by sorry

end PhilipponMultiplicity
