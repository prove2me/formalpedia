-- Prove2me | Theorems.Thm_PrideGuilt_Supplement_proposition_3
-- name    : PrideGuilt.Supplement.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:24:56.757175+00:00
-- url     : https://prove2.me/theorems/66c3c0ad-312f-4d47-8d0f-3509845177fa
-- title:
--   Proposition 3 — the optimum in $\Omega_2$: no recycling on $\Omega_2^0$, perfect recycling on $\Omega_2^1$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the paper's standing assumptions and $\gamma_P,\gamma_G>0$, and write $\tilde\gamma=(1-\tau^0)\gamma_P+\tau^0\gamma_G$. With $p_0=(1-b_1I_G)/(2b_0)+c_n/2$, the highest affordable reward $\bar f$, the equilibrium recycling rate $\tau^*(f)$ of Lemma 1, the demand $D(p,f)$ and the profit $\Pi(p,f)$:
--
--   1. if $(\gamma_P,\gamma_G)\in\Omega_2^0$, then $D(p_0,\bar f)\ge0$, $\Pi(p_0,\bar f)$ is the greatest profit over all $(p,f)\in\mathbb R^2$ with $D(p,f)\ge0$, and $\tau^*(\bar f)=0$;
--   2. if $(\gamma_P,\gamma_G)\in\Omega_2^1$, then the pair
--   $$
--   p^*=\frac{c_u+c_r}{2}+\frac{(b_0+b_1)\bigl(-\gamma_P-\tau^0(\gamma_G-\gamma_P)\bigr)+1-b_1I_G}{2b_0},\qquad f^*=c_r-\gamma_P-\tau^0(\gamma_G-\gamma_P)
--   $$
--   has $D(p^*,f^*)\ge0$, $\Pi(p^*,f^*)$ is the greatest such profit, and $\tau^*(f^*)=1$.
--
--   In $\Omega_2$ guilt is stronger than pride and the manufacturer either accepts the bandwagon toward no recycling or pays the reward that tips it toward perfect recycling.
--
--   **Formalization Note** "Optimal decisions" is stated as attainment of the greatest feasible profit; no uniqueness is claimed (on $\Omega_2^0$ any reward inducing $\tau^*=0$ is also optimal). At $f^*$ the indifference rate of Lemma 1 equals $\tau^0$, the tie that Lemma 1 (ii), as encoded in the base mission's `tauStar`, resolves to $\tau^*=1$. $\Omega_2^0$ is empty when $b_1=b_0$.
--
--   Differences from the source:
--   - correction: Π* is the maximum of Π(p, f) over all (p, f), eq. (5), with no constraint → Π* and "optimal" over (p, f) ∈ ℝ² with D(p, f) ≥ 0 (the published optProfit and its feasible set); reason: as printed, (5) has no maximum when b1 < b0: with τ* = 1 and f → ∞, a negative demand times a negative margin is unbounded (e.g. b0 = 1, b1 = 1/2, cn = 1, cu = 1/2, ce = 3/2, IP = IG = 0 at any (γP, γG)); the base mission declared this correction, footnote 4 and p.12 show feasible demand is intended
--   - reading: Ω2^0 and Ω2^1 defined by their inequalities alone → Ω2^0 and Ω2^1 also require (γP, γG) ∈ Ω2 (in particular γP < γG); reason: the proposition is stated "in Ω2" and the page introduces Ω2^0, Ω2^1 as its two sub-regions
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 3, p.14

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_profit
import Definitions.Def_PrideGuilt_benchPrice
import Definitions.Def_PrideGuilt_Supplement_InOmega2Zero
import Definitions.Def_PrideGuilt_Supplement_InOmega2One
import Definitions.Def_PrideGuilt_Supplement_fBar

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **Proposition 3 (the optimum in `Ω₂`: bandwagons toward no or perfect recycling), with the
base mission's demand constraint `D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 3, p.14 (PDF 15).

Under the standing assumptions, with `γ_P, γ_G > 0`, write `γ̃ = (1 − τ⁰)γ_P + τ⁰γ_G`.
1. On `Ω₂⁰`: the pair `(p₀, f̄)` has nonnegative demand, its profit is the greatest profit over all
   `(p, f) ∈ ℝ²` with `D(p, f) ≥ 0`, and `τ*(f̄) = 0`.
2. On `Ω₂¹`: the pair `p* = (c_u + c_r)/2 + ((b₀ + b₁)(−γ_P − τ⁰(γ_G − γ_P)) + 1 − b₁I_G)/(2b₀)`,
   `f* = c_r − γ_P − τ⁰(γ_G − γ_P)` has nonnegative demand, its profit is the greatest such profit,
   and `τ*(f*) = 1`.

**Formalization Note.** "Optimal decisions" is `IsGreatest` of the feasible profit set; no
uniqueness is claimed (none is on the page; on `Ω₂⁰` any `f` inducing `τ* = 0` is also optimal).
At `f*` the indifference rate equals `τ⁰`, the tie that Lemma 1 (ii), as encoded in the base
mission's `tauStar`, resolves to `τ* = 1`. `Ω₂⁰` is empty when `b₁ = b₀`, so the convention of
`f̄` at `b₁ = b₀` never applies. -/
theorem proposition_3 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG) :
    (InOmega2Zero P γP γG →
      0 ≤ demand P γP γG (benchPrice P) (fBar P γG) ∧
      IsGreatest {π : ℝ | ∃ p f : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}
        (profit P γP γG (benchPrice P) (fBar P γG)) ∧
      tauStar P γP γG (fBar P γG) = 0) ∧
    (InOmega2One P γP γG →
      0 ≤ demand P γP γG
        ((P.cu + cr P) / 2 + ((P.b0 + P.b1) * (-γP - P.τ0 * (γG - γP)) + 1 - P.b1 * P.IG) / (2 * P.b0))
        (cr P - γP - P.τ0 * (γG - γP)) ∧
      IsGreatest {π : ℝ | ∃ p f : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}
        (profit P γP γG
          ((P.cu + cr P) / 2 + ((P.b0 + P.b1) * (-γP - P.τ0 * (γG - γP)) + 1 - P.b1 * P.IG) / (2 * P.b0))
          (cr P - γP - P.τ0 * (γG - γP))) ∧
      tauStar P γP γG (cr P - γP - P.τ0 * (γG - γP)) = 1) := by sorry

end PrideGuilt.Supplement
