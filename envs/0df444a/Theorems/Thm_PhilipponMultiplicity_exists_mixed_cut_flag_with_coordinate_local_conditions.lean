-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_coordinate_local_conditions
-- name    : PhilipponMultiplicity.exists_mixed_cut_flag_with_coordinate_local_conditions
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T17:02:54.254122+00:00
-- url     : https://prove2.me/theorems/a774d51e-7dc7-439a-8661-2093dab4a755
-- title:
--   Mixed cut flags with injective coordinate-local cuts and reduced final quotient
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible subvariety. Let $B\subsetneq W$ be closed, and fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$.
--
--   There are vector subspaces $L_i\subseteq K^{N_i+1}$ with $\dim L_i+\alpha_i=N_i+1$ such that the projective section $Z=W\cap\prod_i\mathbf P(L_i)$ is finite and disjoint from $B$. There are an ordered list of blocks $i_0,\ldots,i_{n-1}$, block-linear forms $P_k$, and actual homogeneous-coordinate cut ideals $J_k$ with
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\quad J_0=I(W),\quad
--   \deg P_k=e_{i_k},\quad J_{k+1}=J_k+(P_k).
--   $$
--   On $W$, the equations $P_k=0$ for $k<n$ define exactly $Z$.
--
--   Write $R=K[X_{ij}]$. For each choice $j=(j_i)_i$ of one coordinate in each block, put $s_j=\prod_iX_{i,j_i}$ and $R_j=R[1/s_j]$. The same flag has these two properties on every such localization:
--
--   1. At each step $k<n$, multiplication by $P_k$ on $R_j/J_kR_j$ is injective. Explicitly, $P_kQ\in J_kR_j$ implies $Q\in J_kR_j$ for every $Q\in R_j$.
--   2. The final ideal $J_nR_j$ is radical, equivalently $R_j/J_nR_j$ is reduced.
--
--   **Formalization Note.** These are finitely many principal opens of the multicone, not degree-zero dehomogenized coordinate rings. Quotients equal to the zero ring, empty sections, and empty cutting lists are allowed. No global reducedness is required away from these opens. The assertion does not assume primary decompositions, associated-prime avoidance, radicality at all relevant primes, equality with a geometric vanishing ideal, or a numerical mixed-degree count.
--
--   This auxiliary geometric existence statement synthesizes generic filter-regular choice with reduced general mixed sections. It is not a verbatim numbered result from a single source. The simultaneous geometric choice and its translation to these explicit localized coordinate rings remain Open.
--
--
--   **Verified closed-point reduction.** The accepted sketch proves a Jacobson-ring membership criterion on principal opens and uses it to propagate injectivity and radicality from maximal localizations. The weak Nullstellensatz identifies the required maximal ideals with evaluation ideals of vectors whose blocks are nonzero. Points outside a cut have the unit localized ideal, so conditions are needed only on its actual geometric points.
--
--   The sole Open dependency is [mixed cut flags with point-local conditions](https://prove2.me/theorems/2f19ff63-31f1-4714-a5cb-c46ac7c7fc78). It supplies the same section and flag, with injectivity at geometric points of each successive cut and reducedness at geometric points of the final cut. No property of an entire coordinate localization is assumed there. The simultaneous geometric choice remains Open; the passage from its point-local conditions to the displayed coordinate-open conditions is proved.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bulletin de la SMF 114 (1986), Lemma 3.1 and the following mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1, p. 3, notes (i)–(ii), p. 4, and Proposition 2.6, p. 6, https://arxiv.org/abs/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, and Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Auxiliary synthesis: a sufficiently general flag is filter-regular on each coordinate localization; transversality on the smooth open of W gives a reduced final section avoiding B and the singular complement. The simultaneous choice and bridge to the displayed multicone localization conditions remain Open.

import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_mixed_cut_flag_with_coordinate_local_conditions
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
            ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let f := algebraMap M.CoordinateRing
                (Localization.Away (∏ i,
                  (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.Away (∏ i,
                (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical) := by sorry

end PhilipponMultiplicity
