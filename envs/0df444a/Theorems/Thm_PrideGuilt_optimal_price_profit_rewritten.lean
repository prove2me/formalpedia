-- Prove2me | Theorems.Thm_PrideGuilt_optimal_price_profit_rewritten
-- name    : PrideGuilt.optimal_price_profit_rewritten
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:47.842236+00:00
-- url     : https://prove2.me/theorems/94cb82e9-8cfc-4603-b1c5-4550a1e9dc0a
-- title:
--   Eqs. (9)–(10) — optimal price and profit in $\Omega_4$ through $\tau^*_m$ and $f^*$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the standing assumptions, $\gamma_P>0$, $\gamma_G>0$ and $(\gamma_P,\gamma_G)\in\Omega_4$, and let $p^*,f^*,\tau^*_m$ be as in Proposition 5. Then
--
--   $$
--   p^*=\frac{1}{2b_0}+\frac{c_n-\tau^*_m(\Delta c-f^*)}{2}-\frac{b_1(I_G+\tau^*_m\gamma_G)}{2b_0},
--   $$
--
--   $$
--   \Pi^*(\gamma_P,\gamma_G)=\frac{1}{4b_0}\Big[1-b_0c_n-b_1I_G+\tau^*_m\big(b_0(\Delta c-f^*)-b_1\gamma_G\big)\Big]^2,
--   $$
--
--   where $\Pi^*$ is the optimal profit over prices and rewards with nonnegative demand, and the consumers' average utility at the optimum is
--
--   $$
--   \bar U(f^*)=f^*-c_e+I_P+(1-\tau^*_m)\gamma_P=-I_G-\tau^*_m\gamma_G .
--   $$
--
--   The closed form (10) for the optimal value is what makes the comparative statics of Theorem 2 explicit: the effect of pride and guilt runs through the remanufacturing benefit $\tau^*_m(b_0(\Delta c-f^*)-b_1\gamma_G)$.
--
--   Differences from the source:
--   - correction: the optimum of (5) (and Π⋆(f) = max_p Π(p,f)) is an unconstrained max over (p, f) → supremum over (p, f) ∈ ℝ² with demand D(p, f) ≥ 0; reason: as printed the max counts a negative demand times a negative margin as profit: it is +∞ for unrestricted f, and with b0 = 1, b1 = 0.5, cn = 1, cu = 0.5, ce = 3, IP = IG = 0, γP = 4, γG = 1 (a point of Ω4) the max over f ≤ c_r is 1.5625 at demand −1.25, independent of γG, contradicting Theorem 2(ii); the paper's footnote 4 (p.13) and p.12 require feasible demand
--   - reading: max over p, f with no stated domain → p and f range over all of ℝ; reason: (5) puts no bound on p or f; f* is negative at some points of Ω4 (−0.5 in the example above), so a sign restriction would falsify Proposition 5
--   - reading: Ū* = f* − c_e + I_p + (1 − τ*)γ_P = −I_G − τ*γ_G → Ubar(f*) = f* − c_e + I_P + (1 − τ*_m)γ_P = −I_G − τ*_mγ_G; reason: the page's I_p is the intrinsic pride I_P (no other I_p exists), and τ* at the optimum is τ*_m by Proposition 5
--   - encoding: τ*(f), the evolutionarily stable rate of Lemma 1 → the Lemma 1 formula tauStar, including its printed values at the endpoints and at τ^0 = τ_m(f); reason: the manufacturer's problem is built on the Lemma 1 formula (p.11); in Ω4 the endpoint values are the limits of τ_m, so the supremum does not depend on them
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eqs. (9)–(10) and the display of Ū*, p.18

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_optProfit
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_tauMStar
import Definitions.Def_PrideGuilt_fStar
import Definitions.Def_PrideGuilt_pStar

namespace PrideGuilt

/-- **Eqs. (9)–(10): the optimal price and the optimal profit in `Ω₄` in terms of `τ*_m` and `f*`,
corrected: demand `D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eqs. (9)–(10) and the display of `Ū*`, p.18 (PDF 19).

Under the standing assumptions, with `γ_P, γ_G > 0` and `(γ_P, γ_G) ∈ Ω₄`:
(9) `p* = 1/(2b₀) + (c_n − τ*_m(Δc − f*))/2 − b₁(I_G + τ*_mγ_G)/(2b₀)`;
(10) `Π* = (1/(4b₀))[1 − b₀c_n − b₁I_G + τ*_m(b₀(Δc − f*) − b₁γ_G)]²`, where `Π*` is the optimal
value (5) over `(p, f) ∈ ℝ²` with `D(p, f) ≥ 0`;
and the average utility at the optimum is `Ū(f*) = f* − c_e + I_P + (1 − τ*_m)γ_P = −I_G − τ*_mγ_G`. -/
theorem optimal_price_profit_rewritten (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP)
    (hγG : 0 < γG) (hΩ : InOmega4 P γP γG) :
    pStar P γP γG = 1 / (2 * P.b0) + (P.cn - tauMStar P γP γG * (dc P - fStar P γP γG)) / 2 -
        P.b1 * (P.IG + tauMStar P γP γG * γG) / (2 * P.b0) ∧
    optProfit P γP γG = 1 / (4 * P.b0) * (1 - P.b0 * P.cn - P.b1 * P.IG +
        tauMStar P γP γG * (P.b0 * (dc P - fStar P γP γG) - P.b1 * γG)) ^ 2 ∧
    Ubar P γP γG (fStar P γP γG) =
        fStar P γP γG - P.ce + P.IP + (1 - tauMStar P γP γG) * γP ∧
    fStar P γP γG - P.ce + P.IP + (1 - tauMStar P γP γG) * γP =
        -P.IG - tauMStar P γP γG * γG := by sorry

end PrideGuilt
