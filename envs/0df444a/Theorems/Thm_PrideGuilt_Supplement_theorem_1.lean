-- Prove2me | Theorems.Thm_PrideGuilt_Supplement_theorem_1
-- name    : PrideGuilt.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:23:36.215839+00:00
-- url     : https://prove2.me/theorems/1abc6e44-9a6a-51ac-a73e-bb01aa9836bd
-- title:
--   Theorem 1 — in $\Omega_4$, signs of $\partial\tau^*_m/\partial\gamma_P$ and $\partial\tau^*_m/\partial\gamma_G$ (corrected: $\gamma_P\ge$ in the second line of (ii))
-- statement:
--   Fix the model parameters other than the socially influenced pride $\gamma_P$ and guilt $\gamma_G$, assume the paper's standing assumptions, $\gamma_P,\gamma_G>0$ and $(\gamma_P,\gamma_G)\in\Omega_4$, and write $d=c_r-\Delta c$ for the degree of reluctance. The interior equilibrium recycling rate of Proposition 5 is
--
--   $$
--   \tau^*_m(\gamma_P,\gamma_G)=\frac{b_0\Delta c-b_0c_r-b_1\gamma_G+b_0\gamma_P}{2b_0(\gamma_P-\gamma_G)} .
--   $$
--
--   It has partial derivatives in $\gamma_P$ and in $\gamma_G$ at this point, and:
--
--   1. $\partial\tau^*_m/\partial\gamma_P\ge0$ if $(1-b_1/b_0)\gamma_G\le d$, and $\partial\tau^*_m/\partial\gamma_P<0$ if $(1-b_1/b_0)\gamma_G>d$; the two conditions are equivalent to $\tau^*_m\le 1/2$ and to $\tau^*_m>1/2$ respectively.
--   2. $\partial\tau^*_m/\partial\gamma_G<0$ if $(1-b_1/b_0)\gamma_P<d$, and $\partial\tau^*_m/\partial\gamma_G\ge0$ if $(1-b_1/b_0)\gamma_P\ge d$; the two conditions are equivalent to $\tau^*_m<b_1/(2b_0)$ and to $\tau^*_m\ge b_1/(2b_0)$.
--   3. $\partial\tau^*_m/\partial\gamma_P\ge\partial\tau^*_m/\partial\gamma_G$ if $(b_0-b_1)(\gamma_P+\gamma_G)\le 2b_0d$, and $\partial\tau^*_m/\partial\gamma_P<\partial\tau^*_m/\partial\gamma_G$ if $(b_0-b_1)(\gamma_P+\gamma_G)>2b_0d$; the two conditions are equivalent to $\tau^*_m\le \tfrac14+\tfrac{b_1}{4b_0}$ and to $\tau^*_m>\tfrac14+\tfrac{b_1}{4b_0}$.
--
--   The theorem shows that each emotion can raise or lower the recycling rate, depending on the strength of the other emotion: a stronger emotion encourages recycling directly but also lets the manufacturer lower the reward.
--
--   **Formalization Note** $\tau^*_m$ is the closed form above (the published `tauMStar`). The partial derivatives are derivatives of the one-variable sections $x\mapsto\tau^*_m(x,\gamma_G)$ and $y\mapsto\tau^*_m(\gamma_P,y)$, and their existence is part of the conclusion. The thresholds are multiplied out by the positive denominators $1-b_1/b_0$ and $b_0-b_1$, so that the case $b_1=b_0$ stays covered.
--
--   Differences from the source:
--   - correction: (ii), second line: ∂τ*_m/∂γG ≥ 0 for γP ≤ (cr − Δc)/(1 − b1/b0), i.e., τ*_m ≥ b1/(2b0) → 0 ≤ ∂τ*_m/∂γG when cr − Δc ≤ (1 − b1/b0)γP, and this condition ↔ b1/(2b0) ≤ τ*_m; reason: the printed ≤ contradicts the first line and its own "i.e."; at b0 = 1, b1 = 1/2, cn = 1, cu = 1/2, ce = 3/2, IP = IG = 0, γP = 3/2, γG = 1/5 (in Ω4, γP ≤ 2) one has τ*_m = 2/13 < 1/4 and ∂τ*_m/∂γG = −25/338 < 0
--   - encoding: thresholds γG ≤ (cr − Δc)/(1 − b1/b0), γP < (cr − Δc)/(1 − b1/b0), γP + γG ≤ 2b0(cr − Δc)/(b0 − b1) → (1 − b1/b0)γG ≤ cr − Δc, (1 − b1/b0)γP < cr − Δc, (b0 − b1)(γP + γG) ≤ 2b0(cr − Δc) (and their negations); reason: identical when b1 < b0; at b1 = b0 (allowed by the standing assumptions) the printed quotients divide by 0 and the multiplied-out forms are the conditions that determine the derivative signs
--   - encoding: ∂τ*_m/∂γP, ∂τ*_m/∂γG → deriv of the sections x ↦ τ*_m(x, γG) at γP and y ↦ τ*_m(γP, y) at γG, with DifferentiableAt in the conclusion; reason: Lean convention for partial derivatives; differentiability is asserted so the junk value 0 cannot satisfy the signs
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Theorem 1, p.17

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_tauMStar

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **Theorem 1 (impact of pride and guilt on the interior recycling rate `τ*_m` in `Ω₄`),
corrected: the second line of (ii) reads `γ_P ≥`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Theorem 1, p.17 (PDF 18).

Fix every parameter except `γ_P, γ_G`, assume the standing assumptions, `γ_P, γ_G > 0` and
`(γ_P, γ_G) ∈ Ω₄`, and write `d = c_r − Δc`. The closed form `τ*_m(γ_P, γ_G)` has partial
derivatives in `γ_P` and in `γ_G` at this point, and
(i) `∂τ*_m/∂γ_P ≥ 0` if `(1 − b₁/b₀)γ_G ≤ d`, `∂τ*_m/∂γ_P < 0` if `(1 − b₁/b₀)γ_G > d`; the
  conditions are equivalent to `τ*_m ≤ 1/2` and `τ*_m > 1/2`;
(ii) `∂τ*_m/∂γ_G < 0` if `(1 − b₁/b₀)γ_P < d`, `∂τ*_m/∂γ_G ≥ 0` if `(1 − b₁/b₀)γ_P ≥ d`; the
  conditions are equivalent to `τ*_m < b₁/(2b₀)` and `τ*_m ≥ b₁/(2b₀)`;
(iii) `∂τ*_m/∂γ_P ≥ ∂τ*_m/∂γ_G` if `(b₀ − b₁)(γ_P + γ_G) ≤ 2b₀d`, `∂τ*_m/∂γ_P < ∂τ*_m/∂γ_G` if
  `(b₀ − b₁)(γ_P + γ_G) > 2b₀d`; the conditions are equivalent to `τ*_m ≤ 1/4 + b₁/(4b₀)` and
  `τ*_m > 1/4 + b₁/(4b₀)`.

**Formalization Note.** (ii) prints `γ_P ≤ (c_r − Δc)/(1 − b₁/b₀)` on its second line; this is a
slip for `≥` (the line's own "i.e., `τ*_m ≥ b₁/(2b₀)`" and the first line force it; with `≤` the
line fails at `b₀ = 1, b₁ = 1/2, c_n = 1, c_u = 1/2, c_e = 3/2, I_P = I_G = 0, γ_P = 3/2, γ_G = 1/5`).
The printed thresholds `γ_G ≤ d/(1 − b₁/b₀)`, `γ_P < d/(1 − b₁/b₀)`, `γ_P + γ_G ≤ 2b₀d/(b₀ − b₁)`
are multiplied out by the positive denominators; this is the same condition when `b₁ < b₀` and
the correct one at `b₁ = b₀`, where the printed quotients divide by `0`. `τ*_m` is the closed
form `tauMStar` of Proposition 5, which is how the paper defines it. The partial derivatives are
`deriv` of the one-variable sections, and their existence is part of the conclusion. -/
theorem theorem_1 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega4 P γP γG) :
    DifferentiableAt ℝ (fun x => tauMStar P x γG) γP ∧
    DifferentiableAt ℝ (fun y => tauMStar P γP y) γG ∧
    -- (i)
    ((1 - P.b1 / P.b0) * γG ≤ cr P - dc P → 0 ≤ deriv (fun x => tauMStar P x γG) γP) ∧
    (cr P - dc P < (1 - P.b1 / P.b0) * γG → deriv (fun x => tauMStar P x γG) γP < 0) ∧
    ((1 - P.b1 / P.b0) * γG ≤ cr P - dc P ↔ tauMStar P γP γG ≤ 1 / 2) ∧
    (cr P - dc P < (1 - P.b1 / P.b0) * γG ↔ 1 / 2 < tauMStar P γP γG) ∧
    -- (ii)
    ((1 - P.b1 / P.b0) * γP < cr P - dc P → deriv (fun y => tauMStar P γP y) γG < 0) ∧
    (cr P - dc P ≤ (1 - P.b1 / P.b0) * γP → 0 ≤ deriv (fun y => tauMStar P γP y) γG) ∧
    ((1 - P.b1 / P.b0) * γP < cr P - dc P ↔ tauMStar P γP γG < P.b1 / (2 * P.b0)) ∧
    (cr P - dc P ≤ (1 - P.b1 / P.b0) * γP ↔ P.b1 / (2 * P.b0) ≤ tauMStar P γP γG) ∧
    -- (iii)
    ((P.b0 - P.b1) * (γP + γG) ≤ 2 * P.b0 * (cr P - dc P) →
        deriv (fun y => tauMStar P γP y) γG ≤ deriv (fun x => tauMStar P x γG) γP) ∧
    (2 * P.b0 * (cr P - dc P) < (P.b0 - P.b1) * (γP + γG) →
        deriv (fun x => tauMStar P x γG) γP < deriv (fun y => tauMStar P γP y) γG) ∧
    ((P.b0 - P.b1) * (γP + γG) ≤ 2 * P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG ≤ 1 / 4 + P.b1 / (4 * P.b0)) ∧
    (2 * P.b0 * (cr P - dc P) < (P.b0 - P.b1) * (γP + γG) ↔
        1 / 4 + P.b1 / (4 * P.b0) < tauMStar P γP γG) := by sorry

end PrideGuilt.Supplement
