-- Prove2me | Theorems.Thm_StrongCosmicCensorship_minkowski_isSpacetime
-- name    : StrongCosmicCensorship.minkowski_isSpacetime
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:05:34.064427+00:00
-- url     : https://prove2.me/theorems/e982e515-0c4f-43a7-84f2-ed9746a54e12
-- title:
--   Minkowski spacetime is a smooth Lorentzian spacetime
-- statement:
--   The Minkowski metric of equation (3.1) of the source,
--   $$m = -dt^2 + dx^2 + dy^2 + dz^2,$$
--   defines a smooth Lorentzian metric on the whole of $\mathbb{R}^{3+1}$: the set $\mathbb{R}^4$ is open, the constant coefficient functions are $C^\infty$, and the constant matrix $\mathrm{diag}(-1,1,1,1)$ has signature $(-,+,+,+)$ at every point.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.1, equation (3.1)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 1** (Section 3.1, equation (3.1)).  Minkowski spacetime is a
spacetime in the sense of the framework. -/
theorem minkowski_isSpacetime : IsSpacetime (univ : Set Coords) minkowski := by sorry

end StrongCosmicCensorship
