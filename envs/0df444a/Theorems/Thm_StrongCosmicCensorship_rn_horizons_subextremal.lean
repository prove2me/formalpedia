-- Prove2me | Theorems.Thm_StrongCosmicCensorship_rn_horizons_subextremal
-- name    : StrongCosmicCensorship.rn_horizons_subextremal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:22:22.979876+00:00
-- url     : https://prove2.me/theorems/0bd6c212-38b0-492f-bc2e-51d327a06f9e
-- title:
--   Sub-extremal Reissner–Nordström has two horizons $r_\pm = M \pm \sqrt{M^2-e^2}$
-- statement:
--   Section 3.3 introduces the Reissner–Nordström family with lapse $1-2M/r+e^2/r^2$ and discusses the sub-extremal range, in which the black hole possesses both an event horizon and, inside it, a Cauchy horizon. For $0<|e|<M$ the lapse vanishes at exactly two positive radii,
--   $$r_\pm = M \pm \sqrt{M^2-e^2}, \qquad 0 < r_- < r_+,$$
--   the outer root $r_+$ being the event horizon and the inner root $r_-$ the Cauchy horizon. It is the Cauchy horizon $r_-$ whose blue-shift instability, discovered by Penrose and Penrose–Simpson, drives the entire discussion of Section 4.
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.3 (Reissner–Nordström, sub-extremal range, event and Cauchy horizons)

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Milestone 9** (Section 3.3).  For a sub-extremal Reissner–Nordström
parameter range `0 < |e| < M`, the lapse `1 - 2M/r + e²/r²` vanishes at exactly
the two radii `r± = M ± √(M² - e²)`, which satisfy `0 < r₋ < r₊`. -/
theorem rn_horizons_subextremal (M e : ℝ) (hM : 0 < M) (he : 0 < |e|) (hsub : |e| < M) :
    0 < rnInnerRadius M e ∧ rnInnerRadius M e < rnOuterRadius M e ∧
      ∀ r : ℝ, r ≠ 0 →
        (rnLapse M e r = 0 ↔ r = rnInnerRadius M e ∨ r = rnOuterRadius M e) := by sorry

end StrongCosmicCensorship
