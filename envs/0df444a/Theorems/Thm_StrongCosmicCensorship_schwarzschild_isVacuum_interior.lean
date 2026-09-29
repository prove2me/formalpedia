-- Prove2me | Theorems.Thm_StrongCosmicCensorship_schwarzschild_isVacuum_interior
-- name    : StrongCosmicCensorship.schwarzschild_isVacuum_interior
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:10:47.085334+00:00
-- url     : https://prove2.me/theorems/1ab33b4f-b358-4b0d-9129-f288db321988
-- title:
--   Schwarzschild solves the vacuum Einstein equations inside the horizon
-- statement:
--   Figure 2 of Section 3.2 presents Schwarzschild as the maximal globally hyperbolic development of a two-ended asymptotically flat hypersurface, with event horizon $\mathcal{H}^+ = \{r=2M\}$ and spacelike singularity $\mathcal{S} = \{r=0\}$. The vacuum equations hold on the black hole interior $\{0<r<2M\}$ just as outside:
--   $$R_{bd}(g_S) = 0 \qquad\text{on } \{0<r<2M\}.$$
--   Inside the horizon $1-2M/r$ is negative, so the roles of $t$ and $r$ are interchanged and the diagonal entries read $(+,-,+,+)$; the signature is unchanged.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.2, equation (3.2), Figure 2 (event horizon $\mathcal{H}^+=\{r=2M\}$, singularity $\mathcal{S}=\{r=0\}$)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 6** (Section 3.2).  The Schwarzschild metric solves the vacuum
Einstein equations on the black hole interior `{0 < r < 2M}` as well. -/
theorem schwarzschild_isVacuum_interior (M : ℝ) (hM : 0 < M) :
    IsVacuum (schwarzschildInterior M) (schwarzschild M) := by sorry

end StrongCosmicCensorship
