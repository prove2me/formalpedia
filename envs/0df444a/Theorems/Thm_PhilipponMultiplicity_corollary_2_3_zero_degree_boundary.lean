-- Prove2me | Theorems.Thm_PhilipponMultiplicity_corollary_2_3_zero_degree_boundary
-- name    : PhilipponMultiplicity.corollary_2_3_zero_degree_boundary
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-30T09:24:17.249977+00:00
-- url     : https://prove2.me/theorems/78050513-db6b-4eb0-8a49-9bd2183a61f0
-- title:
--   Corollary 2.3: the zero-degree boundary branch
-- statement:
--   **Accepted proof-sketch; geometric coordinate-projection transport remains Open.** The Lean reduction proves that zero block degrees remove the corresponding polynomial variables, derives a positive-degree obstruction criterion from Theorem 2.1, lifts the sampling grid and final translate, and chooses a uniform constant over all nonempty factor selections. It explicitly handles S=0 and radii below one. The sole Open child is [coordinate projection of contact and subgroup obstructions](p2m:theorem/ad1b3d37-eeb2-4245-acc0-baa62f364ee5).
--
--   This is the zero-degree branch of Corollary 2.3. Let $K$ be a Philippon base field and let $G=\prod_i G_i$ have disjoint factors, with $n_i=\dim G_i$ and $n=\sum_i n_i$. There is a constant $c>0$, depending only on the embedded product, with the following property.
--
--   Let $A$ be an analytic subgroup, let $\gamma_1,\ldots,\gamma_l\in G$, let $S\ge0$, and let $T$ and the entries of $D=(D_i)$ be natural numbers. Suppose at least one $D_i=0$. Write $\Gamma_S=\{\sum_j a_j\gamma_j: a_j\in\mathbb N,\ a_j\le S\}$. For each tuple $0\le r_i\le n_i$, let $\sigma_r$ and $\rho_r$ be, respectively, the minimum analytic codimension of $A\cap H$ in $A$ and the minimum rank of the image of the sampling group in $G/H$, over algebraic subgroups $H$ not containing $A$ and with factor codimensions at least $r_i$.
--
--   Suppose a nonzero multihomogeneous polynomial $P$ of multidegree $D$ has order at least $nT+1$ along $A$ at every point of $\Gamma_{nS}$ and, for every such $r$,
--
--   $$c\prod_i D_i^{r_i}\le (T+1)^{\sigma_r}S^{\rho_r}.$$
--
--   Then $P$ vanishes on an entire translate of $A$:
--
--   $$\exists g\in G,\qquad g+A\subseteq Z_G(P).$$
--
--   This isolates the remaining boundary branch after the positive-degree reduction of Corollary 2.3. It retains $S=0$, redundant analytic parameters, and every tuple of nonnegative multidegrees with at least one zero entry.
--
--   **Formalization Note** The minima and vanishing order are exactly the mission's existing definitions; a natural-number infimum of an empty family is zero, and natural powers use $0^0=1$. This is an open specialization of the published target, not a strengthened hypothesis in Corollary 2.3 itself.
--
--   The formal statement is unchanged. The remaining child constructs the projected analytic subgroup with equal contact orders and lifts individual algebraic obstruction subgroups with their tangent-codimension and quotient-rank data. It assumes no multiplicity estimate or vanishing conclusion. The reduction does not compare empty-family minima.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp. 360–361, Corollary 2.3 and its proof, restricted to multidegrees with at least one zero entry. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Corollaries

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem corollary_2_3_zero_degree_boundary
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∃ i, D i = 0) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P := by sorry

end PhilipponMultiplicity
