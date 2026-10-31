-- Prove2me | Theorems.Thm_PeriodicEval_objective_summable
-- name    : PeriodicEval.objective_summable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:58.921994+00:00
-- url     : https://prove2.me/theorems/2e6bfd48-03f5-4124-b941-f7c4cc026aab
-- title:
--   Proof of Proposition 1, (25) — summability, Fubini and the bound on the objective
-- statement:
--   Under the standing assumptions, let $x>0$, $X\in\mathcal A_0(x)$ and $\xi_i:=e^{-\beta T_i}U(X_{T_i}-\gamma X_{T_{i-1}})$, $i\ge1$. Then
--
--   1. $\sum_{i=1}^\infty E[\xi_i^+]<\infty$ and $\sum_{i=1}^\infty E[\xi_i^-]<\infty$;
--   2. $\sum_i\xi_i$ is integrable and, by Fubini's theorem, $E\big[\sum_{i=1}^\infty\xi_i\big]=\sum_{i=1}^\infty E[\xi_i]$;
--   3. (25):
--   $$\sum_{i=1}^\infty E[\xi_i]\le\frac{e^{-(\beta-h)\tau}}{1-e^{-(\beta-h)\tau}}x^\alpha.$$
--
--   This makes the objective of problem (4) a genuine expectation for every admissible portfolio and bounds it uniformly.
--
--   **Formalization Note** $E[\xi^+]$ and $E[\xi^-]$ are Lebesgue integrals of $\max(\xi,0)$ and $\max(-\xi,0)$.
--
--   Differences from the source:
--   - encoding: E[ξ_i^±] and the index i = 1, 2, … → lower Lebesgue integrals of max(±ξ, 0); index i + 1 with i ∈ ℕ; reason: the expectation of a nonnegative variable; same series
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Proposition 1, eq. (25) and the sentence after it, p.42

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Summability and Fubini for the objective (4), SSRN 3971852 (June 20, 2023), proof of
Proposition 1, (25), p.42. For `x > 0` and `X ∈ A_0(x)`, with
`ξ_i := e^{−βT_i} U(X_{T_i} − γX_{T_{i−1}})`, `i ≥ 1`:
1. `∑_i E[ξ_i⁺] < ∞` and `∑_i E[ξ_i⁻] < ∞`;
2. `∑_i ξ_i` is integrable and `E[∑_{i=1}^∞ ξ_i] = ∑_{i=1}^∞ E[ξ_i]` (Fubini);
3. `∑_{i=1}^∞ E[ξ_i] ≤ e^{−(β−h)τ}/(1 − e^{−(β−h)τ}) x^α` ((25)).

**Formalization Note** `E[ξ⁺]`, `E[ξ⁻]` are lower Lebesgue integrals of `max(ξ, 0)`,
`max(−ξ, 0)`, so their finiteness is not a junk-value artifact. The index `i = 1, 2, …` is
`i + 1` with `i : ℕ`. -/
theorem objective_summable (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (X : ℝ≥0 → Ω → ℝ)
    (hX : X ∈ admissible p P ℱ B 0 x) :
    let ξ : ℕ → Ω → ℝ := fun i ω =>
      Real.exp (-(p.β * (p.T (i + 1) : ℝ))) * U p (X (p.T (i + 1)) ω - p.γ * X (p.T i) ω)
    (∑' i, ∫⁻ ω, ENNReal.ofReal (ξ i ω) ∂P) < ∞ ∧
    (∑' i, ∫⁻ ω, ENNReal.ofReal (-ξ i ω) ∂P) < ∞ ∧
    Integrable (fun ω => ∑' i, ξ i ω) P ∧
    objective p P X = ∑' i, ∫ ω, ξ i ω ∂P ∧
    (∑' i, ∫ ω, ξ i ω ∂P) ≤
      Real.exp (-((p.β - p.h) * p.τ)) / (1 - Real.exp (-((p.β - p.h) * p.τ))) * x ^ p.α := by sorry

end PeriodicEval
