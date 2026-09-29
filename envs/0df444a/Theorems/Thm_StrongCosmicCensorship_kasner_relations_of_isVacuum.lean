-- Prove2me | Theorems.Thm_StrongCosmicCensorship_kasner_relations_of_isVacuum
-- name    : StrongCosmicCensorship.kasner_relations_of_isVacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:26:57.391215+00:00
-- url     : https://prove2.me/theorems/f507e6b6-57cd-4a44-ad71-ec7a421b5845
-- title:
--   A Ricci-flat Kasner metric with positive exponents satisfies the Kasner relations
-- statement:
--   The converse of the preceding milestone. Section 4 notes in connection with Theorem 4.11 that the Kasner exponents are constrained; for strictly positive exponents the constraint is exactly the pair of Kasner relations. If
--   $$g = -dt^2 + \sum_i t^{2p_i}(dx^i)^2$$
--   with every $p_i>0$ is Ricci-flat on $\{t>0\}$, then
--   $$\sum_i p_i = 1 \qquad\text{and}\qquad \sum_i p_i^2 = 1 .$$
--   The positivity hypothesis is genuinely needed: the flat case $p_1=p_2=p_3=0$ is Ricci-flat, being Minkowski spacetime in disguise, yet has $\sum_i p_i = 0 \ne 1$.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 4 and Theorem 4.11 (Kasner exponents $p_i$; the Kasner relations)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 12** (Section 4).  Conversely, a Kasner metric with strictly
positive exponents that solves the vacuum Einstein equations on `{t > 0}` must
satisfy the Kasner relations. -/
theorem kasner_relations_of_isVacuum (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hvac : IsVacuum kasnerRegion (kasner p)) :
    KasnerRelations p := by sorry

end StrongCosmicCensorship
