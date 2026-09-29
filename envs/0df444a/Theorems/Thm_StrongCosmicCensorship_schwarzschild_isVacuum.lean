-- Prove2me | Theorems.Thm_StrongCosmicCensorship_schwarzschild_isVacuum
-- name    : StrongCosmicCensorship.schwarzschild_isVacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:09:51.14112+00:00
-- url     : https://prove2.me/theorems/1b4dc888-66e8-4d58-ae7d-0731d2b01401
-- title:
--   Schwarzschild solves the vacuum Einstein equations outside the horizon
-- statement:
--   The Schwarzschild metric is described in Section 3.2 as a family of “black hole solutions to (2.4) in a vacuum”. On the exterior region $\{r>2M\}$ its Ricci tensor vanishes identically:
--   $$R_{bd}(g_S) = 0 .$$
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.2, equation (3.2), with equation (2.4)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 5** (Section 3.2).  The Schwarzschild metric solves the vacuum
Einstein equations on the exterior region. -/
theorem schwarzschild_isVacuum (M : ℝ) (hM : 0 < M) :
    IsVacuum (schwarzschildExterior M) (schwarzschild M) := by sorry

end StrongCosmicCensorship
