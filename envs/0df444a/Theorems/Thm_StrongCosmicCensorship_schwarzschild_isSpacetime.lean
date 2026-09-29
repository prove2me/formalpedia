-- Prove2me | Theorems.Thm_StrongCosmicCensorship_schwarzschild_isSpacetime
-- name    : StrongCosmicCensorship.schwarzschild_isSpacetime
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:09:24.04201+00:00
-- url     : https://prove2.me/theorems/c7be604a-1f77-436a-b3a1-5d1a73dda7fa
-- title:
--   The Schwarzschild exterior is a smooth Lorentzian spacetime
-- statement:
--   For mass parameter $M>0$, the Schwarzschild metric of equation (3.2),
--   $$g_S = -\Big(1-\frac{2M}{r}\Big)dt^2 + \Big(1-\frac{2M}{r}\Big)^{-1}dr^2 + r^2\big(d\theta^2+\sin^2\theta\,d\varphi^2\big),$$
--   is a smooth Lorentzian metric on the exterior region $\{r>2M\}$, taken inside the angular chart $0<\theta<\pi$ where the standard spherical coordinates are nondegenerate. On that region $1-2M/r$ is positive, so the four diagonal entries are $(-,+,+,+)$ as required.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.2, equation (3.2)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 4** (Section 3.2, equation (3.2)).  For positive mass the
Schwarzschild metric is a smooth Lorentzian metric on the exterior region
`{r > 2M}` of the chart `0 < θ < π`. -/
theorem schwarzschild_isSpacetime (M : ℝ) (hM : 0 < M) :
    IsSpacetime (schwarzschildExterior M) (schwarzschild M) := by sorry

end StrongCosmicCensorship
