-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_filter_regular_mixed_section
-- name    : PhilipponMultiplicity.exists_filter_regular_mixed_section
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T14:00:30.21014+00:00
-- url     : https://prove2.me/theorems/9cb97862-bbc3-49d4-bd20-d0aa77d62e44
-- title:
--   Filter-regular mixed linear sections with reduced final ideal
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{N_i}$, and let $W\subseteq M$ be closed and irreducible. Fix integers $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$, and a proper closed subset $B\subset W$.
--
--   There exist linear subspaces $L_i$ of codimensions $\alpha_i$ such that $Z=W\cap\prod_iL_i$ is finite and disjoint from $B$, together with an ordered list of block indices $i_0,\ldots,i_{n-1}$, block-linear forms $P_0,\ldots,P_{n-1}$, and homogeneous cut ideals $J_0,\ldots,J_n$ satisfying
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   Each multiplication by $P_k$ is injective on the quotient in every sufficiently large block degree: for all such $D$ and every multihomogeneous $Q$ of degree $D$,
--   $$
--   P_kQ\in J_k\quad\Longrightarrow\quad Q\in J_k.
--   $$
--   The final cut ideal agrees with the reduced vanishing ideal of $Z$ in every sufficiently large block degree:
--   $$
--   (J_n)_D=I(Z)_D\qquad(D\gg0).
--   $$
--   The thresholds may depend on the cut. This is an auxiliary existence statement for general linear sections: filter regularity controls the Hilbert-polynomial exact sequences, while the final equality retains the reduced intersection needed for point counting. It contains no assertion about mixed Hilbert coefficients or the numerical degree of the section. The empty section is allowed.
--
--   **Formalization Note.** Linear subspaces are vector submodules of dimension $N_i+1-\alpha_i$. The list records the block of each equation. The ideal and polynomial sequences are indexed by natural numbers, with conditions only on the finite prefix. Large-degree ideal equality is stated through actual homogeneous polynomial membership; no saturation or reducedness certificate is added to the original ambient-space definitions.
--
--   **Verified algebraic reduction.** An accepted proof-sketch reduces this statement to [reduced mixed sections with primary-prime avoidance](https://prove2.me/theorems/59f8cca7-05a4-4593-a731-c93ebd29ca5f). The reduction proves that irrelevant homogeneous primary components contain every sufficiently large homogeneous piece; avoidance of all relevant primary radicals then gives the required eventual injectivity. Relevant embedded components are retained. It also proves that equality of localized ideals at every relevant prime gives equality of homogeneous pieces in all sufficiently large multidegrees. The remaining child supplies the geometric section, the primary-avoidance conditions, and the final reduced local ideal. It contains no eventual Hilbert-function or numerical-degree assertion. The geometric selection remains Open, and the formal statement is unchanged.
-- source:
--   Philippon (1986), Lemma 3.1 and its exact-sequence proof, p. 363, and the paragraph preceding Lemma 3.2, p. 364, computing mixed coefficients with general linear sections: https://numdam.org/articles/10.24033/bsmf.2060/ . Auxiliary formulation of the remaining generic-choice, filter-regularity, reduced-intersection and proper-boundary-avoidance step; not a verbatim numbered theorem.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree

theorem exists_filter_regular_mixed_section
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
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L))) := by sorry

end PhilipponMultiplicity
