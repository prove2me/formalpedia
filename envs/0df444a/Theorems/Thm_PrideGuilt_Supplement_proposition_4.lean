-- Prove2me | Theorems.Thm_PrideGuilt_Supplement_proposition_4
-- name    : PrideGuilt.Supplement.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:25:54.857589+00:00
-- url     : https://prove2.me/theorems/fcde5526-e2fe-448d-8290-c453a8b33729
-- title:
--   Proposition 4 — in $\Omega_3$ the optimum $f^*=c_r-\gamma_G$ induces perfect recycling (corrected: demand $D\ge0$)
-- statement:
--   Assume the paper's standing assumptions, $\gamma_P,\gamma_G>0$ and $(\gamma_P,\gamma_G)\in\Omega_3$. Then the pair
--
--   $$
--   p^*=\frac{b_0(c_u+c_r-\gamma_G)-b_1\gamma_G-b_1I_G+1}{2b_0},\qquad f^*=c_r-\gamma_G
--   $$
--
--   has nonnegative demand $D(p^*,f^*)\ge0$, its profit $\Pi(p^*,f^*)$ is the greatest profit over all $(p,f)\in\mathbb R^2$ with $D(p,f)\ge0$, and it induces perfect recycling: $\tau^*(f^*)=1$, where $\tau^*$ is the equilibrium recycling rate of Lemma 1.
--
--   When pride is stronger than guilt and the degree of reluctance is low, the manufacturer pays exactly the reward at which every consumer recycles.
--
--   **Formalization Note** "Optimally sets" is stated as attainment of the greatest feasible profit; no uniqueness is claimed. $\tau^*$ is the base mission's `tauStar` (the Lemma 1 formula), which gives $1$ at the endpoint $f=c_r-\gamma_G$.
--
--   Differences from the source:
--   - correction: Π* is the maximum of Π(p, f) over all (p, f), eq. (5), with no constraint → Π* and "optimal" over (p, f) ∈ ℝ² with D(p, f) ≥ 0 (the published optProfit and its feasible set); reason: as printed, (5) has no maximum when b1 < b0: with τ* = 1 and f → ∞, a negative demand times a negative margin is unbounded (e.g. b0 = 1, b1 = 1/2, cn = 1, cu = 1/2, ce = 3/2, IP = IG = 0 at any (γP, γG)); the base mission declared this correction, footnote 4 and p.12 show feasible demand is intended
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 4, p.15

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_profit
import Definitions.Def_PrideGuilt_Supplement_InOmega3

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **Proposition 4 (perfect recycling in `Ω₃`), with the base mission's demand constraint
`D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 4, p.15 (PDF 16).

Under the standing assumptions, with `γ_P, γ_G > 0` and `(γ_P, γ_G) ∈ Ω₃`, the pair
`p* = (b₀(c_u + c_r − γ_G) − b₁γ_G − b₁I_G + 1)/(2b₀)`, `f* = c_r − γ_G` has nonnegative demand,
its profit is the greatest profit over all `(p, f) ∈ ℝ²` with `D(p, f) ≥ 0`, and it induces
perfect recycling, `τ*(f*) = 1`.

**Formalization Note.** "Optimally sets" is `IsGreatest` of the feasible profit set; no uniqueness
is claimed. `τ*` is the base mission's `tauStar` (the Lemma 1 formula), which gives `1` at the
endpoint `f = c_r − γ_G`; the claim is about that map, not about stability in the sense of
Definition 1 at this endpoint. -/
theorem proposition_4 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega3 P γP γG) :
    0 ≤ demand P γP γG
      ((P.b0 * (P.cu + cr P - γG) - P.b1 * γG - P.b1 * P.IG + 1) / (2 * P.b0)) (cr P - γG) ∧
    IsGreatest {π : ℝ | ∃ p f : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}
      (profit P γP γG
        ((P.b0 * (P.cu + cr P - γG) - P.b1 * γG - P.b1 * P.IG + 1) / (2 * P.b0)) (cr P - γG)) ∧
    tauStar P γP γG (cr P - γG) = 1 := by sorry

end PrideGuilt.Supplement
