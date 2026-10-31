-- Prove2me | Theorems.Thm_PrideGuilt_benchmark_optimum
-- name    : PrideGuilt.benchmark_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:44.531686+00:00
-- url     : https://prove2.me/theorems/5a525873-6802-4c8f-b528-dede5a6d836e
-- title:
--   Eqs. (6)–(7) — the benchmark optimum $p_0$ and $\Pi_0$ without remanufacturing
-- statement:
--   Assume the standing assumptions. Without remanufacturing the demand is $\tilde D(p)=1-b_0p-b_1I_G$ and the profit $\tilde\Pi(p)=\tilde D(p)(p-c_n)$. Then the price
--
--   $$
--   p_0=\frac{1-b_1I_G}{2b_0}+\frac{c_n}{2}
--   $$
--
--   has nonnegative demand, is the unique maximizer of $\tilde\Pi$ over the prices with $\tilde D(p)\ge0$, and
--
--   $$
--   \Pi_0=\tilde\Pi(p_0)=\frac{\tilde D(p_0)^2}{b_0}=\frac{(1-b_1I_G-b_0c_n)^2}{4b_0}.
--   $$
--
--   This benchmark is the profit the manufacturer must beat for remanufacturing to pay (Proposition 1).
--
--   Differences from the source:
--   - encoding: the optimal selling price and profit of Π̃ over all prices → Π_0 is the supremum of Π̃ over prices with D̃(p) ≥ 0, and p_0 its unique maximizer there; reason: matches the demand constraint of the corrected (5); the unconstrained maximizer p_0 has D̃(p_0) = (1 − b1IG − b0cn)/2 ≥ 0, so value and maximizer are unchanged
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eqs. (6)–(7), p.12

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_benchPrice
import Definitions.Def_PrideGuilt_benchOpt

namespace PrideGuilt

/-- **Eqs. (6)–(7): the benchmark optimum without remanufacturing.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eqs. (6)–(7), p.12 (PDF 13).

Under the standing assumptions, the price `p₀ = (1 − b₁I_G)/(2b₀) + c_n/2` has nonnegative
benchmark demand, is the unique maximizer of `Π̃(p) = D̃(p)(p − c_n)` over the prices with
`D̃(p) ≥ 0`, and `Π₀ = Π̃(p₀) = D̃(p₀)²/b₀ = (1 − b₁I_G − b₀c_n)²/(4b₀)`.

**Formalization Note.** `Π₀` is `benchOpt`, the supremum over `D̃ ≥ 0`; the constraint does not
bind because `D̃(p₀) = (1 − b₁I_G − b₀c_n)/2 ≥ 0`. -/
theorem benchmark_optimum (P : Params) (hP : Standing P) :
    0 ≤ benchDemand P (benchPrice P) ∧
    (∀ p : ℝ, 0 ≤ benchDemand P p → benchProfit P p ≤ benchProfit P (benchPrice P)) ∧
    (∀ p : ℝ, 0 ≤ benchDemand P p → benchProfit P p = benchProfit P (benchPrice P) →
        p = benchPrice P) ∧
    benchOpt P = benchProfit P (benchPrice P) ∧
    benchProfit P (benchPrice P) = benchDemand P (benchPrice P) ^ 2 / P.b0 ∧
    benchDemand P (benchPrice P) ^ 2 / P.b0 = (1 - P.b1 * P.IG - P.b0 * P.cn) ^ 2 / (4 * P.b0) := by sorry

end PrideGuilt
