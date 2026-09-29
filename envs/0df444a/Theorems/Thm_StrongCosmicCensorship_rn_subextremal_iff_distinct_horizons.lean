-- Prove2me | Theorems.Thm_StrongCosmicCensorship_rn_subextremal_iff_distinct_horizons
-- name    : StrongCosmicCensorship.rn_subextremal_iff_distinct_horizons
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:22:44.580984+00:00
-- url     : https://prove2.me/theorems/ad01cfb0-cd5e-4a98-89e3-7d25d92b3f96
-- title:
--   Sub-extremality is equivalent to distinct Reissner–Nordström horizons
-- statement:
--   Section 3.3 works throughout in the sub-extremal range, the condition distinguishing a black hole with two distinct horizons from the extremal case in which they coincide. Within the physical range $e^2\le M^2$ and for $M>0$,
--   $$|e| < M \iff r_- < r_+ ,$$
--   so sub-extremality is exactly the separation of the Cauchy horizon from the event horizon. The extremal case $|e| = M$ collapses $r_-=r_+=M$.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.3 (sub-extremal versus extremal Reissner–Nordström)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 10** (Section 3.3).  Sub-extremality is exactly the condition
under which the two horizons are distinct: `|e| < M` iff `r₋ < r₊`, given
`0 < M`. -/
theorem rn_subextremal_iff_distinct_horizons (M e : ℝ) (hM : 0 < M) (he : e ^ 2 ≤ M ^ 2) :
    |e| < M ↔ rnInnerRadius M e < rnOuterRadius M e := by sorry

end StrongCosmicCensorship
