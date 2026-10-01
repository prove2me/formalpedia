-- Prove2me | Theorems.Thm_PhilipponMultiplicity_coordinate_projection_tangent_kernel
-- name    : PhilipponMultiplicity.coordinate_projection_tangent_kernel
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T10:35:55.967639+00:00
-- url     : https://prove2.me/theorems/6e69a173-9be0-4937-9e06-fcde7737853a
-- title:
--   Coordinate projection: tangent kernels of subgroup preimages
-- statement:
--   **Proved by explicit polynomial specialization and differentiation.** A complete Lean proof freezes omitted coordinates at an identity lift, proves membership in the actual projected vanishing ideal, splits the differential into retained and omitted parts, and extends the homogeneous equation test to the ideal by the product rule. There are no Open theorem dependencies.
--
--   Let $K$ be a Philippon base field, let $G$ be an embedded product of commutative algebraic groups, and choose a nonempty subset $I$ of its factors. Let $\pi:G\to G_I$ be the coordinate projection, retaining the original embeddings. For an analytic subgroup parametrization $A$, form the explicit projected parametrization $B=\pi\circ A$ on the same parameter ball. Its lifts are defined by restricting those of $A$ at the section that inserts the identity in omitted factors. In particular, the base lift of $B$ is exactly the restriction of the base lift of $A$.
--
--   For every closed algebraic subgroup $H\subseteq G_I$, the tangent kernels satisfy
--   $$
--   \ker\bigl(dB\bmod T_0H\bigr)
--   \subseteq
--   \ker\bigl(dA\bmod T_0(\pi^{-1}H)\bigr).
--   $$
--   Both sides are subspaces of the original parameter space. Explicitly, if a parameter vector annihilates at zero the differentials of the pullbacks of every polynomial in the actual multihomogeneous vanishing ideal of $H$, then it annihilates the corresponding differentials for every polynomial in the vanishing ideal of $\pi^{-1}(H)$.
--
--   The tangent kernels here are the existing intersections of differential kernels over those actual ideals. No tangent-space presentation, ideal-generation identity, or smoothness certificate is supplied as an assumption. No injectivity or minimality of the analytic parametrization, and no disjoint-factor hypothesis, is required.
--
--   This theorem completes the tangent-space input in the coordinate-projection transport proof. Construction of $B$, equality of its carrier with $\pi(A)$, contact-order preservation, algebraicity of subgroup preimages, preservation of selected factor codimensions and sampling quotient ranks, and inheritance of disjoint factors are proved in the parent submission. The assertion concerns first-order tangent transport only; it assumes no multiplicity estimate.
-- source:
--   Auxiliary tangent-space statement for the coordinate-projection treatment of zero multidegrees in P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp.360–361, Corollary 2.3; analytic subgroup and contact conventions on pp.357–358. This is a supporting formalization lemma, not a separately numbered theorem of the paper. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_ProjectedAnalytic

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- Projected tangent directions annihilating the subgroup equations also
annihilate the equations of its actual inverse image. -/
theorem coordinate_projection_tangent_kernel
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (s : GroupFactorSelection G)
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup s.group) :
    (s.projectedAnalytic A).tangentKernel H.carrier ≤
      A.tangentKernel (s.project ⁻¹' H.carrier) := by sorry

end PhilipponMultiplicity
