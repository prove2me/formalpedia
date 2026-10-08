-- Prove2me | Theorems.Thm_SelfDualLP_Output_theorem_8
-- name    : SelfDualLP.Output.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:57.986975+00:00
-- url     : https://prove2.me/theorems/6be2df5a-b116-4837-9f23-25d2db30af83
-- title:
--   Theorem 8 — τᵏ ≥ (1 − 2β)/(eᵀx̄ + eᵀs̄ + 1) if (LP) has an optimum; otherwise κᵏ ≥ (1 − 2β)ε/(n + 1) and τᵏ/θᵏ is bounded
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ be real data, and let $(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)_{k\ge0}$ be the iterates of the Mizuno–Todd–Ye predictor–corrector algorithm applied to the homogeneous self-dual program (HLP) under the choice (7), with $\beta=1/4$.
--
--   1. If (LP) possesses an optimal solution, then
--   $$
--   \tau^k\ge\frac{1-2\beta}{e^T\bar x+e^T\bar s+1}\qquad\text{for all }k,
--   $$
--   where $\bar x$ and $(\bar y,\bar s)$ are **any** optimal solution pair for (LP) and (LD).
--   2. Otherwise there is a fixed number $\varepsilon>0$, independent of $k$, such that for all $k$
--   $$
--   \kappa^k\ge\frac{(1-2\beta)\varepsilon}{n+1}
--   $$
--   and
--   $$
--   \frac{1-2\beta}{2(n+1)}\le\frac{1-2\beta}{\kappa^k}\le\frac{\tau^k}{\theta^k}\le\frac{1+2\beta}{\kappa^k}\le\frac{(n+1)(1+2\beta)}{(1-2\beta)\varepsilon}.
--   $$
--
--   So either $\tau^k$ stays bounded away from zero, which happens exactly when (LP) has an optimal solution, or $\tau^k$ and $\theta^k$ tend to zero at the same rate while $\kappa^k$ stays bounded away from zero. This lets one decide the status of (LP) from an approximate iterate, without running the algorithm to an exact solution.
--
--   **Formalization Note** $\beta$ is the algorithm's fixed parameter $1/4$, so $1-2\beta=1/2$ and $1+2\beta=3/2$. "Otherwise" is the negation of "(LP) possesses an optimal solution": it covers infeasible (LP), and feasible but unbounded (LP). The number $\varepsilon$ is chosen after the data and the sequence and before $k$; it may depend on the instance. The chain is kept as printed, with divisions; all denominators are positive along the sequence ($\kappa^k>0$, $\theta^k=\mu^k>0$ on $\mathcal N(2\beta)$), so no link holds because of Lean's convention $x/0=0$. The statement quantifies over predictor–corrector sequences; on an instance where the maximum in (13) is not attained, no such sequence exists and the statement is vacuous there.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 63, Theorem 8; DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 8 (p. 63), with `β = 1/4`. Let `(yᵏ, xᵏ, τᵏ, θᵏ, sᵏ, κᵏ)` be the iterates of the
predictor–corrector algorithm on (HLP) under (7).
* If (LP) possesses an optimal solution, then `τᵏ ≥ (1 − 2β)/(eᵀx̄ + eᵀs̄ + 1)` for all `k`,
  where `x̄` and `(ȳ, s̄)` are any optimal solution pair for (LP) and (LD);
* otherwise there is a fixed `ε > 0`, independent of `k`, such that for all `k`
  `κᵏ ≥ (1 − 2β)ε/(n + 1)` and
  `(1 − 2β)/(2(n + 1)) ≤ (1 − 2β)/κᵏ ≤ τᵏ/θᵏ ≤ (1 + 2β)/κᵏ ≤ (n + 1)(1 + 2β)/((1 − 2β)ε)`. -/
theorem theorem_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : ℕ → HLPPoint m n) (hz : IsPCSequence A b c z) :
    (SelfDualLP.Complexity.LPHasSolution A b c →
      ∀ (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ),
        SelfDualLP.Complexity.LPOptimal A b c xbar → SelfDualLP.Complexity.LDOptimal A b c ybar sbar →
        ∀ k, (1 - 2 * beta) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) ≤ (z k).τ) ∧
    (¬ SelfDualLP.Complexity.LPHasSolution A b c →
      ∃ ε : ℝ, 0 < ε ∧ ∀ k,
        (1 - 2 * beta) * ε / ((n : ℝ) + 1) ≤ (z k).κ ∧
        (1 - 2 * beta) / (2 * ((n : ℝ) + 1)) ≤ (1 - 2 * beta) / (z k).κ ∧
        (1 - 2 * beta) / (z k).κ ≤ (z k).τ / (z k).θ ∧
        (z k).τ / (z k).θ ≤ (1 + 2 * beta) / (z k).κ ∧
        (1 + 2 * beta) / (z k).κ ≤ ((n : ℝ) + 1) * (1 + 2 * beta) / ((1 - 2 * beta) * ε)) := by sorry
end SelfDualLP.Output
