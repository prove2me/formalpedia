-- Prove2me | Theorems.Thm_PrideGuilt_Supplement_proposition_2
-- name    : PrideGuilt.Supplement.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:24:18.240805+00:00
-- url     : https://prove2.me/theorems/2c227c68-4628-401e-a606-9e44e9692357
-- title:
--   Proposition 2 — in $\Omega_1$ remanufacturing is not profitable and $\Pi^*=\Pi_0$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the paper's standing assumptions, $\gamma_P,\gamma_G>0$, $\gamma_P\ne\gamma_G$ and $(\gamma_P,\gamma_G)\in\Omega_1$. Let $p_0=(1-b_1I_G)/(2b_0)+c_n/2$ be the benchmark price, $\Pi_0$ the benchmark profit without remanufacturing, $\tau^*(f)$ the equilibrium recycling rate of Lemma 1 at reward $f$, $D(p,f)$ the demand and $\Pi(p,f)$ the manufacturer's profit. Then:
--
--   1. for every reward $f$ with $\tau^*(f)=0$ (no recycling), the pair $(p_0,f)$ has $D(p_0,f)\ge0$ and
--   $$
--   \Pi(p_0,f)=\max\{\Pi(p,f') : (p,f')\in\mathbb R^2,\ D(p,f')\ge0\};
--   $$
--   2. the optimal profit equals the benchmark profit, $\Pi^*=\Pi_0$;
--   3. if $b_1<b_0$, the highest affordable reward $\bar f$ induces no recycling: $\tau^*(\bar f)=0$.
--
--   The proposition describes the region where the degree of reluctance is so high that the manufacturer runs no recycling program and earns the benchmark profit.
--
--   **Formalization Note** "Optimally sets $p^*=p_0$ without any recycling program" is stated for every reward $f$ that induces $\tau^*(f)=0$ (for instance any $f\le c_r-\max(\gamma_P,\gamma_G)$); no uniqueness is claimed, as on the page. $\Pi^*$ is the base mission's `optProfit`.
--
--   Differences from the source:
--   - correction: Π* is the maximum of Π(p, f) over all (p, f), eq. (5), with no constraint → Π* and "optimal" over (p, f) ∈ ℝ² with D(p, f) ≥ 0 (the published optProfit and its feasible set); reason: as printed, (5) has no maximum when b1 < b0: with τ* = 1 and f → ∞, a negative demand times a negative margin is unbounded (e.g. b0 = 1, b1 = 1/2, cn = 1, cu = 1/2, ce = 3/2, IP = IG = 0 at any (γP, γG)); the base mission declared this correction, footnote 4 and p.12 show feasible demand is intended
--   - reading: "the manufacturer optimally sets p* = p0 without any recycling program, and the resulting ESE for recycling rate is τ* = 0" → for every f with τ*(f) = 0, (p0, f) has D ≥ 0 and attains the greatest feasible profit; and Π* = Π0; reason: "without any recycling program" fixes no particular reward; every reward that induces τ* = 0 gives the same demand and margin
--   - reading: "f̄ is insufficient to induce any recycling" → b1 < b0 → τ*(f̄) = 0; reason: f̄ = max(f_p, f_m) and f_p divides by 1 − b1/b0, so f̄ is undefined at b1 = b0; every other clause is stated for all b1 ≤ b0
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 2, p.13; f̄, p.13

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_optProfit
import Definitions.Def_PrideGuilt_benchPrice
import Definitions.Def_PrideGuilt_benchOpt
import Definitions.Def_PrideGuilt_Supplement_InOmega1
import Definitions.Def_PrideGuilt_Supplement_fBar

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **Proposition 2 (no remanufacturing in `Ω₁`), with the base mission's demand constraint
`D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 2, p.13 (PDF 14).

Under the standing assumptions, with `γ_P, γ_G > 0`, `γ_P ≠ γ_G` and `(γ_P, γ_G) ∈ Ω₁`:
1. for every reward `f` that induces no recycling (`τ*(f) = 0`), the pair `(p₀, f)` has
   nonnegative demand and its profit is the greatest profit over all `(p, f') ∈ ℝ²` with
   `D(p, f') ≥ 0`;
2. the optimal profit equals the benchmark profit, `Π* = Π₀` (remanufacturing is not profitable);
3. if `b₁ < b₀`, the highest affordable reward `f̄` induces no recycling, `τ*(f̄) = 0`.

**Formalization Note.** "Optimally sets `p* = p₀` without any recycling program" is stated as
`IsGreatest` of the feasible profit set at `(p₀, f)` for every `f` with `τ*(f) = 0` (such `f`
exist: `f ≤ c_r − max(γ_P, γ_G)`). No uniqueness is claimed, as on the page. `Π*` is the base
mission's `optProfit` (supremum over `D ≥ 0`). Clause 3 assumes `b₁ < b₀` because `f̄` divides
by `1 − b₁/b₀`. -/
theorem proposition_2 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hne : γP ≠ γG) (hΩ : InOmega1 P γP γG) :
    (∀ f : ℝ, tauStar P γP γG f = 0 →
        0 ≤ demand P γP γG (benchPrice P) f ∧
        IsGreatest {π : ℝ | ∃ p f' : ℝ, 0 ≤ demand P γP γG p f' ∧ π = profit P γP γG p f'}
          (profit P γP γG (benchPrice P) f)) ∧
    optProfit P γP γG = benchOpt P ∧
    (P.b1 < P.b0 → tauStar P γP γG (fBar P γG) = 0) := by sorry

end PrideGuilt.Supplement
