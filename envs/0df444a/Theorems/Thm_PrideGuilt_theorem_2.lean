-- Prove2me | Theorems.Thm_PrideGuilt_theorem_2
-- name    : PrideGuilt.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:18.599784+00:00
-- url     : https://prove2.me/theorems/d688909d-59df-45e0-b775-b42800e6f54d
-- title:
--   Theorem 2 — in $\Omega_4$ pride raises the optimal profit, guilt lowers it iff $\tau^*_m<b_1/b_0$ (corrected: demand $D\ge0$)
-- statement:
--   Fix every parameter except the social pride $\gamma_P$ and guilt $\gamma_G$, and let $\Pi^*(\gamma_P,\gamma_G)$ be the manufacturer's optimal profit over prices and rewards $(p,f)\in\mathbb R^2$ with nonnegative demand. Assume the standing assumptions, $\gamma_P>0$, $\gamma_G>0$ and $(\gamma_P,\gamma_G)\in\Omega_4$, and write $\tau^*_m=\dfrac{b_0\Delta c-b_0c_r-b_1\gamma_G+b_0\gamma_P}{2b_0(\gamma_P-\gamma_G)}$. Then $\Pi^*$ has both partial derivatives at $(\gamma_P,\gamma_G)$, and:
--
--   1. $\dfrac{\partial\Pi^*}{\partial\gamma_P}\ge0$;
--   2. $\dfrac{\partial\Pi^*}{\partial\gamma_G}<0$ if $(b_0-2b_1)\gamma_P+b_1\gamma_G<b_0(c_r-\Delta c)$, and $\dfrac{\partial\Pi^*}{\partial\gamma_G}\ge0$ if $(b_0-2b_1)\gamma_P+b_1\gamma_G\ge b_0(c_r-\Delta c)$; moreover $(b_0-2b_1)\gamma_P+b_1\gamma_G<b_0(c_r-\Delta c)$ holds iff $\tau^*_m<b_1/b_0$;
--   3. $\dfrac{\partial\Pi^*}{\partial\gamma_P}\ge\dfrac{\partial\Pi^*}{\partial\gamma_G}$ if $b_0\gamma_G-b_1\gamma_P\le b_0(c_r-\Delta c)$, and $\dfrac{\partial\Pi^*}{\partial\gamma_P}<\dfrac{\partial\Pi^*}{\partial\gamma_G}$ if $b_0\gamma_G-b_1\gamma_P>b_0(c_r-\Delta c)$; moreover $b_0\gamma_G-b_1\gamma_P\le b_0(c_r-\Delta c)$ holds iff $\tau^*_m\le(b_0+b_1)/(2b_0)$.
--
--   So in the region of moderately high difficulty of remanufacturing where pride outweighs guilt, stronger pride never hurts the manufacturer, while stronger guilt hurts exactly when the optimal recycling rate is below $b_1/b_0$, and guilt helps more than pride exactly when that rate exceeds $(b_0+b_1)/(2b_0)$.
--
--   **Formalization Note** The partial derivatives are the derivatives of the one-variable sections $x\mapsto\Pi^*(x,\gamma_G)$ at $\gamma_P$ and $y\mapsto\Pi^*(\gamma_P,y)$ at $\gamma_G$; their existence is part of the conclusion. Each "i.e." equivalence is stated once as an iff; its negation is the "i.e." of the second line.
--
--   Differences from the source:
--   - correction: the optimum of (5) (and Π⋆(f) = max_p Π(p,f)) is an unconstrained max over (p, f) → supremum over (p, f) ∈ ℝ² with demand D(p, f) ≥ 0; reason: as printed the max counts a negative demand times a negative margin as profit: it is +∞ for unrestricted f, and with b0 = 1, b1 = 0.5, cn = 1, cu = 0.5, ce = 3, IP = IG = 0, γP = 4, γG = 1 (a point of Ω4) the max over f ≤ c_r is 1.5625 at demand −1.25, independent of γG, contradicting Theorem 2(ii); the paper's footnote 4 (p.13) and p.12 require feasible demand
--   - reading: max over p, f with no stated domain → p and f range over all of ℝ; reason: (5) puts no bound on p or f; f* is negative at some points of Ω4 (−0.5 in the example above), so a sign restriction would falsify Proposition 5
--   - generalization: the discussion of §4 is restricted to the part of Ω4 where p* ≥ 0 (p.13) → all of Ω4, no p* ≥ 0 hypothesis; reason: Theorem 2 holds on all of Ω4 (Π* = K*²/(4b0) with K* = 1 − b1IG − b0cn + b0a²/(4s) > 0, a = γP − (c_r − Δc) − (b1/b0)γG > 0, s = γP − γG > 0); it specializes to the source's statement on the p* ≥ 0 part
--   - encoding: ∂Π*/∂γP and ∂Π*/∂γG → deriv of the one-variable sections x ↦ Π*(x, γG) and y ↦ Π*(γP, y), with their differentiability asserted; reason: partial derivatives of a function of two variables; differentiability rules out Lean's junk value deriv = 0
--   - encoding: τ*(f), the evolutionarily stable rate of Lemma 1 → the Lemma 1 formula tauStar, including its printed values at the endpoints and at τ^0 = τ_m(f); reason: the manufacturer's problem is built on the Lemma 1 formula (p.11); in Ω4 the endpoint values are the limits of τ_m, so the supremum does not depend on them
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Theorem 2, p.18

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_optProfit
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_tauMStar

namespace PrideGuilt

/-- **Theorem 2 (impact of pride and guilt on the optimal profit in `Ω₄`), corrected: demand
`D ≥ 0` in (5).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Theorem 2, p.18 (PDF 19).

Fix every parameter except `γ_P, γ_G`, assume the standing assumptions, `γ_P, γ_G > 0` and
`(γ_P, γ_G) ∈ Ω₄`, and write `d = c_r − Δc`. The optimal profit `Π*(γ_P, γ_G)` has partial
derivatives in `γ_P` and in `γ_G` at this point, and
(i) `∂Π*/∂γ_P ≥ 0`;
(ii) `∂Π*/∂γ_G < 0` if `(b₀ − 2b₁)γ_P + b₁γ_G < b₀d`, and `∂Π*/∂γ_G ≥ 0` if
  `(b₀ − 2b₁)γ_P + b₁γ_G ≥ b₀d`; the first condition holds iff `τ*_m < b₁/b₀`;
(iii) `∂Π*/∂γ_P ≥ ∂Π*/∂γ_G` if `b₀γ_G − b₁γ_P ≤ b₀d`, and `∂Π*/∂γ_P < ∂Π*/∂γ_G` if
  `b₀γ_G − b₁γ_P > b₀d`; the first condition holds iff `τ*_m ≤ (b₀ + b₁)/(2b₀)`.

**Formalization Note.** `Π*` is `optProfit`, the supremum of `Π(p, f)` over `(p, f) ∈ ℝ²` with
`D(p, f) ≥ 0` (correction; as printed, (5) is maximized at a negative demand and the theorem fails
at `b₀ = 1`, `b₁ = 0.5`, `c_n = 1`, `c_u = 0.5`, `c_e = 3`, `I_P = I_G = 0`, `γ_P = 4`, `γ_G = 1`).
The partial derivatives are `deriv` of the one-variable sections `x ↦ Π*(x, γ_G)` and
`y ↦ Π*(γ_P, y)`, whose differentiability is part of the conclusion. Each "i.e." equivalence is
one `↔`; its negation is the "i.e." of the second line. No `p* ≥ 0` restriction is assumed. -/
theorem theorem_2 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega4 P γP γG) :
    DifferentiableAt ℝ (fun x => optProfit P x γG) γP ∧
    DifferentiableAt ℝ (fun y => optProfit P γP y) γG ∧
    0 ≤ deriv (fun x => optProfit P x γG) γP ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG < 0) ∧
    (P.b0 * (cr P - dc P) ≤ (P.b0 - 2 * P.b1) * γP + P.b1 * γG →
        0 ≤ deriv (fun y => optProfit P γP y) γG) ∧
    ((P.b0 - 2 * P.b1) * γP + P.b1 * γG < P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG < P.b1 / P.b0) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) →
        deriv (fun y => optProfit P γP y) γG ≤ deriv (fun x => optProfit P x γG) γP) ∧
    (P.b0 * (cr P - dc P) < P.b0 * γG - P.b1 * γP →
        deriv (fun x => optProfit P x γG) γP < deriv (fun y => optProfit P γP y) γG) ∧
    (P.b0 * γG - P.b1 * γP ≤ P.b0 * (cr P - dc P) ↔
        tauMStar P γP γG ≤ (P.b0 + P.b1) / (2 * P.b0)) := by sorry

end PrideGuilt
