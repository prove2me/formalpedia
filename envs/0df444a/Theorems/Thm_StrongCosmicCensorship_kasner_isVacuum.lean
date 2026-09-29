-- Prove2me | Theorems.Thm_StrongCosmicCensorship_kasner_isVacuum
-- name    : StrongCosmicCensorship.kasner_isVacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:23:43.168435+00:00
-- url     : https://prove2.me/theorems/1eddb7e9-6c4a-40bc-819b-aa3206140309
-- title:
--   Kasner metrics satisfying the Kasner relations are Ricci-flat
-- statement:
--   The Kasner metrics appear in Section 4 as the local model for the spacelike singularities constructed in Theorem 4.11, where the source notes that the Kasner exponents $p_i$ are constrained. The Kasner metric
--   $$g = -dt^2 + t^{2p_1}(dx^1)^2 + t^{2p_2}(dx^2)^2 + t^{2p_3}(dx^3)^2$$
--   solves the vacuum Einstein equations on $\{t>0\}$ whenever the exponents satisfy the Kasner relations
--   $$p_1+p_2+p_3 = 1, \qquad p_1^2+p_2^2+p_3^2 = 1 .$$
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 4 and Theorem 4.11 (Kasner exponents $p_i$; the Kasner relations)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 11** (Section 4, the setting of Theorem 4.11).  A Kasner metric
whose exponents satisfy the Kasner relations `Σ pᵢ = Σ pᵢ² = 1` solves the vacuum
Einstein equations on `{t > 0}`. -/
theorem kasner_isVacuum (p : Fin 3 → ℝ) (hp : KasnerRelations p) :
    IsVacuum kasnerRegion (kasner p) := by sorry

end StrongCosmicCensorship
