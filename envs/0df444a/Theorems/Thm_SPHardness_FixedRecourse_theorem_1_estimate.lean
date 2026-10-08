-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_theorem_1_estimate
-- name    : SPHardness.FixedRecourse.theorem_1_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:40.533252+00:00
-- url     : https://prove2.me/theorems/a4e80542-9498-4505-a1da-e270b13f90a4
-- title:
--   Theorem 1, pp. 7–8 — finite difference estimates knapsack volume
-- statement:
--   Let $\alpha\in\mathbb R^k_+$ have final weight $\alpha_k>0$, let $\beta\ge0$ and $\delta>0$. Put $h=2\sqrt{\delta}$, and take $\delta$-accurate values $q_0$ and $q_1$ of $\mathcal Q(\alpha,\beta)$ and $\mathcal Q(\alpha,\beta+h)$. Then
--   $$\left|\frac{q_1-q_0}{h}+1-V(\alpha,\beta)\right|\le\sqrt{\delta}\left(1+\frac1{\alpha_k}\right).$$
--   If all weights are positive and $\delta$ satisfies the strict threshold (7), this bound is strictly below the volume tolerance in (3).
--
--   The estimate converts an expected-recourse oracle into the approximate volume values used by Lemma 1. **Formalization Note** The step $h$ is positive because $\delta>0$.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 7–8, proof of Theorem 1, (7)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem theorem_1_estimate {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hαk : 0 < lastWeight hk α)
    (β δ : ℝ) (hβ : 0 ≤ β) (hδ0 : 0 < δ)
    (q₀ q₁ : ℝ)
    (hq₀ : |q₀ - expRecourse α β| ≤ δ)
    (hq₁ : |q₁ - expRecourse α (β + 2 * Real.sqrt δ)| ≤ δ) :
    |(q₁ - q₀) / (2 * Real.sqrt δ) + 1 - vol α β| ≤
        Real.sqrt δ * (1 + 1 / lastWeight hk α) ∧
      ((∀ j, 0 < α j) → δ < delta7 α (lastWeight hk α) →
        Real.sqrt δ * (1 + 1 / lastWeight hk α) < eps3 α) := by sorry
end SPHardness.FixedRecourse
