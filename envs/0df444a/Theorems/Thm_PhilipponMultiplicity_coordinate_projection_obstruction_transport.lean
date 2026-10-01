-- Prove2me | Theorems.Thm_PhilipponMultiplicity_coordinate_projection_obstruction_transport
-- name    : PhilipponMultiplicity.coordinate_projection_obstruction_transport
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T09:57:57.104524+00:00
-- url     : https://prove2.me/theorems/ad1b3d37-eeb2-4245-acc0-baa62f364ee5
-- title:
--   Coordinate projections: analytic contact and subgroup obstructions
-- statement:
--   **Accepted proof-sketch; only tangent-kernel transport remains Open.** The Lean reduction explicitly constructs the projected analytic parametrization on the original parameter ball and proves carrier equality and contact-order preservation. It constructs actual algebraic subgroup preimages, proves inheritance of disjoint factors, identifies selected factor codimensions, and proves equality of sampling quotient ranks. Its sole Open child is [tangent kernels of subgroup preimages](p2m:theorem/6e69a173-9be0-4937-9e06-fcde7737853a).
--
--   Let $G=\prod_i G_i$ be an embedded product of commutative algebraic groups over a Philippon base field, with disjoint factors. Choose a nonempty set $I$ of its factors, keep their original embeddings, and let
--   $$
--   G_I=\prod_{i\in I}G_i,\qquad \pi:G\longrightarrow G_I
--   $$
--   be the coordinate projection. For an exponent tuple $r$ on $I$, write $\widetilde r$ for its extension by zero outside $I$. Then $G_I$ has disjoint factors, and every analytic subgroup $A$ of $G$ admits an analytic subgroup $B$ of $G_I$ with
--   $$
--   B=\pi(A).
--   $$
--   For every multihomogeneous polynomial $Q$ on $G_I$ and every $g\in G$, its actual pullback by coordinate renaming satisfies
--   $$
--   \operatorname{ord}_{A,g}(\pi^*Q)=\operatorname{ord}_{B,\pi(g)}(Q).
--   $$
--   For each algebraic subgroup $H\subseteq G_I$, there is an algebraic subgroup $H'\subseteq G$ whose carrier is exactly $\pi^{-1}(H)$. With $r_i=\operatorname{codim}_{G_i}\operatorname{pr}_i(H)$ on $I$, it satisfies
--   $$
--   \widetilde r_i\le\operatorname{codim}_{G_i}\operatorname{pr}_i(H'),\qquad
--   \operatorname{codim}_{A}(A\cap H')\le\operatorname{codim}_{B}(B\cap H).
--   $$
--   For every finite list of sampling generators $\gamma$, the corresponding quotient ranks are equal:
--   $$
--   \operatorname{rank}_{\mathbb Z}\langle\gamma\bmod H'\rangle
--   =\operatorname{rank}_{\mathbb Z}\langle\pi(\gamma)\bmod H\rangle.
--   $$
--   The codimensions use the existing Hilbert dimensions of factor projections and the existing tangent-kernel definition for analytic subgroups. The rank is the rank of the subgroup generated in the actual quotient. No injectivity or minimality of the analytic parametrization is required.
--
--   This is the remaining geometric input in a reduction of the zero-degree branch of Philippon's Corollary 2.3. It transports individual obstruction subgroups, so it makes no assertion comparing empty-family infima. The polynomial support reduction, grid lifting, uniform choice of the numerical constant and multiplicity-estimate argument are separate proved parts of the parent sketch. This statement assumes no multiplicity estimate or vanishing conclusion.
--
--   The formal statement is unchanged. The remaining inclusion is between tangent kernels defined from the actual vanishing ideals on the same parameter space. The analytic-codimension inequality is proved from that inclusion by finite-dimensional rank monotonicity. No additional hypothesis is imposed on the original theorem.
-- source:
--   Geometric projection input used to treat zero entries in the multidegree in P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp.360–361, Corollary 2.3. This is an auxiliary formalization statement, not a separately numbered assertion of the paper. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_FactorProjection

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- Coordinate projection transports analytic contact and the actual
algebraic subgroup obstructions. No multiplicity estimate is assumed. -/
theorem coordinate_projection_obstruction_transport
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G)
    (s : GroupFactorSelection G) :
    HasDisjointFactors s.group ∧
    ∀ A : AnalyticSubgroup G, ∃ B : AnalyticSubgroup s.group,
      B.carrier = s.project '' A.carrier ∧
      (∀ (Q : s.group.CoordinateRing) (D : s.group.FactorIndex → ℕ),
        IsMultihomogeneousOfDegree s.group Q D → ∀ g : G.Point,
        vanishingOrder A (MvPolynomial.rename s.coordinateIndex Q) g =
          vanishingOrder B Q (s.project g)) ∧
      (∀ H : AlgebraicSubgroup s.group, ∃ H' : AlgebraicSubgroup G,
        H'.carrier = s.project ⁻¹' H.carrier ∧
        (∀ i, s.extendExponent (factorCodimension s.group H) i ≤
          factorCodimension G H' i) ∧
        analyticCodimension A H'.carrier ≤ analyticCodimension B H.carrier ∧
        ∀ (l : ℕ) (γ : Fin l → G.Point),
          samplingQuotientRank γ H' = samplingQuotientRank (fun i => s.project (γ i)) H) := by sorry

end PhilipponMultiplicity
