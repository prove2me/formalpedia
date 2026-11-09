-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_3_1
-- name    : SpatialHalfspace.FullLabels.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:24.730787+00:00
-- url     : https://prove2.me/theorems/2c74895a-4ab4-440c-ad92-5a53dcf0be88
-- title:
--   Lemma 3.1 — Midpoint prediction and excess risk
-- statement:
--   Let $z_0,z_1\in\mathbb R^2$ be orthogonal unit vectors, $a=(z_0+z_1)/2$, and let $Q_s$, $Q_{s,t}=(Q_s+Q_t)/2$ be the midpoint switch (feature masses $(\zeta,\alpha,\rho,\rho)$ at $(0,a,z_0,z_1)$, label probabilities $0,1,\tfrac12,0$ at $0,a,z_s,z_{1-s}$; $\alpha=1/64$, $\rho=4\alpha$). For every $s\in\{0,1\}$ and every homogeneous halfspace $h\in H_2$, writing $(A,B_0,B_1)=(h(a),h(z_0),h(z_1))$,
--
--   $$R_{Q_{s,s}}(h)=2\alpha+\alpha(1-A)+4\alpha B_{1-s},\qquad R^*_{Q_{s,s}}(H_2)=2\alpha,\tag{13}$$
--
--   $$R_{Q_{s,1-s}}(h)=2\alpha+\alpha(1-A)+2\alpha(B_0+B_1),\qquad R^*_{Q_{s,1-s}}(H_2)=3\alpha.\tag{14}$$
--
--   Therefore, for all $s,t\in\{0,1\}$ and $h\in H_2$, with $Z(s,t)=1\{s=t\}$,
--
--   $$R_{Q_{s,t}}(h)-R^*_{Q_{s,t}}(H_2)\ \ge\ \alpha\,1\{h(a)\ne Z(s,t)\}.\tag{15}$$
--
--   This is the two-terminal gadget: the optimal midpoint prediction of a halfspace encodes whether the two terminal bits are equal.
--
--   Differences from the source:
--
--   - encoding: (A, B₀, B₁) ∈ {0,1}, B_{1−s}, the indicator 1{h(a) ≠ Z(s,t)} → Bool predictions converted by bitR; B_{1−s} written as h(z₀) if s = 1 and h(z₁) if s = 0; reason: identification of {0,1} with Bool
--   - encoding: R*_Q(H₂) = inf over H₂ → infimum over all weight vectors w ∈ ℝ² of the risk of x ↦ 1{⟨w,x⟩ > 0}; reason: H₂ is exactly this set of classifiers
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 8, PDF p. 9, Lemma 3.1, eqs. (13)–(15), PDF p. 9

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 3.1 (Midpoint prediction and excess risk), printed p. 8. For orthogonal unit
vectors `z₀, z₁ ∈ ℝ²`, `a = (z₀ + z₁)/2`, every `s ∈ {0,1}` and `h ∈ H₂` with
`(A, B₀, B₁) = (h(a), h(z₀), h(z₁))`: (13) `R_{Q_{s,s}}(h) = 2α + α(1 − A) + 4αB_{1−s}`,
`R*_{Q_{s,s}}(H₂) = 2α`; (14) `R_{Q_{s,1−s}}(h) = 2α + α(1 − A) + 2α(B₀ + B₁)`,
`R*_{Q_{s,1−s}}(H₂) = 3α`; and (15) `R_{Q_{s,t}}(h) − R*_{Q_{s,t}}(H₂) ≥ α 1{h(a) ≠ Z(s,t)}`. -/
theorem lemma_3_1 (z0 z1 : Vec 2) (hz0 : ‖z0‖ = 1) (hz1 : ‖z1‖ = 1) (horth : ⟪z0, z1⟫_ℝ = 0) :
    (∀ s : Bool, ∀ h ∈ homHalfspaces 2,
      risk (switchPair z0 z1 s s) h =
          2 * alpha + alpha * (1 - bitR (h (midpoint2 z0 z1))) +
            4 * alpha * bitR (if s then h z0 else h z1) ∧
        optRisk (switchPair z0 z1 s s) = 2 * alpha ∧
        risk (switchPair z0 z1 s (!s)) h =
          2 * alpha + alpha * (1 - bitR (h (midpoint2 z0 z1))) +
            2 * alpha * (bitR (h z0) + bitR (h z1)) ∧
        optRisk (switchPair z0 z1 s (!s)) = 3 * alpha) ∧
    ∀ s t : Bool, ∀ h ∈ homHalfspaces 2,
      alpha * bitR (decide (h (midpoint2 z0 z1) ≠ Zbit s t)) ≤
        risk (switchPair z0 z1 s t) h - optRisk (switchPair z0 z1 s t) := by sorry

end SpatialHalfspace.FullLabels
