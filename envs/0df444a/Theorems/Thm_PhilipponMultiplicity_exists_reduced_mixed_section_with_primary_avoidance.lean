-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_reduced_mixed_section_with_primary_avoidance
-- name    : PhilipponMultiplicity.exists_reduced_mixed_section_with_primary_avoidance
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T14:34:52.300066+00:00
-- url     : https://prove2.me/theorems/59f8cca7-05a4-4593-a731-c93ebd29ca5f
-- title:
--   Reduced mixed sections with primary-prime avoidance
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{N_i}$, and let $W\subseteq M$ be closed and irreducible. Fix integers $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$, and a proper closed subset $B\subset W$.
--
--   There exist linear subspaces $L_i$ of codimensions $\alpha_i$ such that $Z=W\cap\prod_iL_i$ is finite and avoids $B$. They can be accompanied by a list of block indices $i_0,\ldots,i_{n-1}$, block-linear equations $P_k$, and cut ideals $J_k$ with
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   For each $k<n$, there is a finite minimal multihomogeneous primary decomposition
--   $$
--   J_k=\bigcap_j Q_{kj}
--   $$
--   such that $P_k$ avoids every relevant primary radical:
--   $$
--   \mathfrak b\not\subseteq\sqrt{Q_{kj}}
--   \quad\Longrightarrow\quad P_k\notin\sqrt{Q_{kj}}.
--   $$
--   Here $\mathfrak b$ is the multiprojective irrelevant ideal. Relevant embedded components are included in this condition. Irrelevant components need not be avoided.
--
--   The final ideal and the reduced vanishing ideal of $Z$ agree at every relevant prime of the homogeneous coordinate ring $R$:
--   $$
--   J_nR_{\mathfrak p}=I(Z)R_{\mathfrak p}
--   \qquad\text{if }\mathfrak b\not\subseteq\mathfrak p.
--   $$
--   This is the geometric general-position input for the mixed-section construction. It retains the actual local scheme structure of the final intersection and imposes no assertion about Hilbert functions, large-degree homogeneous pieces, or numerical mixed degrees. The empty section and the empty list are allowed.
--
--   **Formalization Note.** The primary decompositions are the existing finite minimal homogeneous decompositions. Localization is at every relevant prime, not only at closed points or minimal primes. Linear subspaces are represented by vector submodules of dimension $N_i+1-\alpha_i$. This is an auxiliary combined formulation of the geometric selection step, not a verbatim numbered theorem in any one source.
--
--
--   **Verified algebraic reduction.** The accepted sketch proves a localized multiprojective Nullstellensatz: at every relevant prime $\mathfrak p$, the localized geometric vanishing ideal of a homogeneous cut is contained in $\sqrt{IR_{\mathfrak p}}$. Relevance supplies a product of coordinate variables that is a unit after localization; the ordinary affine Nullstellensatz supplies the radical membership. If the cut is reduced there, this proves equality of the two localized ideals.
--
--   The only Open dependency is [mixed cut flags reduced on the relevant locus](https://prove2.me/theorems/b6f41518-ee71-44f1-ab50-6b0f11374892). It asks for the geometric section, its explicit equations, primary-prime avoidance, and local reducedness. A proved induction identifies the zero set of the cut chain with the chosen section. No equality with the section's vanishing ideal is assumed in the child. Irrelevant components and empty sections are allowed. The geometric selection remains Open.
-- source:
--   Philippon (1986), pp. 363–364, Lemma 3.1 and the following paragraph on general mixed linear sections, https://numdam.org/articles/10.24033/bsmf.2060/ . Primary-prime avoidance: Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1 (p. 3), Proposition 2.4 (p. 5), and Proposition 2.6 (p. 6), https://arxiv.org/abs/0901.3825 . Reduced general sections: S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, and Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Auxiliary synthesis for products of projective spaces: the simultaneous generic choice, boundary avoidance, and equality of the actual localized final ideal remain to be proved.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_reduced_mixed_section_with_primary_avoidance
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
            ∃ A : PrimaryDecomposition M (J k), ∀ j : Fin A.count,
              Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
              P k ∉ (A.component j).radical) ∧
          (∀ q : PrimeSpectrum M.CoordinateRing,
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
            (J l.length).map
                (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)) =
              (M.vanishingIdeal (linearSlice M W L)).map
                (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))) := by sorry

end PhilipponMultiplicity
