-- Prove2me | Theorems.Thm_TightQLearning_theorem_2
-- name    : TightQLearning.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:19.422708+00:00
-- url     : https://prove2.me/theorems/84edd6b2-d889-4e0b-a00e-bb18e1f6d99c
-- title:
--   Theorem 2 — synchronous Q-learning is $\varepsilon$-accurate in $\ell_\infty$ with probability $1-\delta$ once $T\ge c_3\log^4T\log(|S||A|T/\delta)/((1-\gamma)^4\varepsilon^2)$
-- statement:
--   There is $\bar c>0$ such that for all $0<c_2\le c_1\le\bar c$ there is $c_3>0$ with the following property. Consider a finite discounted MDP with rewards in $[0,1]$, and any $\delta\in(0,1)$, $\varepsilon\in(0,1]$, $\gamma\in[\frac12,1)$. Let $T\ge2$, and let the learning rates satisfy, for $0\le t\le T$,
--   $$\frac1{1+\frac{c_1(1-\gamma)T}{\log^3T}}\le\eta_t\le\frac1{1+\frac{c_2(1-\gamma)t}{\log^3T}}.$$
--   Assume that
--   $$T\ge\frac{c_3(\log^4T)\big(\log\frac{|\mathcal S||\mathcal A|T}\delta\big)}{(1-\gamma)^4\varepsilon^2}$$
--   and that $0\le Q_0(s,a)\le\frac1{1-\gamma}$ for all $(s,a)$. Then Algorithm 1, run on independent samples $s_t(s,a)\sim P(\cdot\mid s,a)$, achieves
--   $$\max_{(s,a)\in\mathcal S\times\mathcal A}\big|Q_T(s,a)-Q^\star(s,a)\big|\le\varepsilon$$
--   with probability at least $1-\delta$.
--
--   This sample complexity is the first to break the $\frac{|\mathcal S||\mathcal A|}{(1-\gamma)^5\varepsilon^2}$ barrier for vanilla Q-learning, and it is the paper's main upper bound.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - encoding: samples s_t(s,a) ∼ P(·|s,a), independent, for t = 1,…,T → IsGenerativeModel on an arbitrary probability space: joint independence over (t,s,a) with 1 ≤ t ≤ T, law P(·|s,a), discrete σ-algebra on X; reason: this is the page's sampling model; the algorithm never reads a sample outside that range
--   - encoding: (16a) divides by log³T, which is undefined at T = 1 → the hypothesis 2 ≤ T; reason: it excludes only T = 0 and T = 1, where the printed condition is undefined; Lean's x/0 = 0 would make the statement false there (verified)
--   - reading: "some small enough universal constants c₁ ≥ c₂ > 0", "some sufficiently large universal constant c₃" → ∃ c̄ > 0, ∀ c₁ c₂ with 0 < c₂ ≤ c₁ ≤ c̄, ∃ c₃ > 0, before every instance quantity; reason: "small enough" means every small pair works; c₃ must follow c₂, since as c₂ → 0 rates near 1 become admissible; this implies the literal ∃ c₁ c₂ c₃
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Theorem 2, (16a), (16b), (17), p.9

import Mathlib
import Definitions.Def_TightQLearning_syncQ
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_RateBand
import Definitions.Def_TightQLearning_IsGenerativeModel

open QLearning.Convergence MeasureTheory

namespace TightQLearning

/-- Theorem 2 (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.9): for `δ ∈ (0,1)`, `ε ∈ (0,1]`,
`γ ∈ [1/2,1)`, with learning rates obeying (16a), `T ≥ c₃ (log⁴T)(log(|S||A|T/δ))/((1−γ)⁴ε²)`
(16b) and `0 ≤ Q₀ ≤ 1/(1−γ)`, Algorithm 1 achieves `max_{(s,a)} |Q_T(s,a) − Q⋆(s,a)| ≤ ε` (17) with
probability at least `1 − δ`.

**Formalization Note.** "Small enough universal constants `c₁ ≥ c₂ > 0`" reads: every such pair
below a universal `c̄`. `c₃` is chosen after `c₁, c₂` and before every instance quantity. `2 ≤ T`
excludes the undefined `log³T = 0` in (16a). `log` is natural; `|S||A|` is
`Fintype.card X * Fintype.card A`. The rates are deterministic and may depend on the instance. -/
theorem theorem_2 :
    ∃ cbar : ℝ, 0 < cbar ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ ≤ cbar →
      ∃ c₃ : ℝ, 0 < c₃ ∧
        ∀ (X A : Type) [Fintype X] [DecidableEq X] [Nonempty X]
          [Fintype A] [DecidableEq A] [Nonempty A]
          (M : FiniteMDP X A) (_hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1)
          (δ ε γ : ℝ) (_hδ : 0 < δ ∧ δ < 1) (_hγ : 1 / 2 ≤ γ ∧ γ < 1) (_hε : 0 < ε ∧ ε ≤ 1)
          (T : ℕ) (_hT : 2 ≤ T) (η : ℕ → ℝ) (_hη : RateBand c₁ c₂ γ T η)
          (_hTlarge : (T : ℝ) ≥ c₃ * (Real.log T ^ 4 *
            Real.log ((Fintype.card X : ℝ) * (Fintype.card A : ℝ) * (T : ℝ) / δ)) /
              ((1 - γ) ^ 4 * ε ^ 2))
          (Q0 : X → A → ℝ) (_hQ0 : ∀ s a, 0 ≤ Q0 s a ∧ Q0 s a ≤ 1 / (1 - γ))
          {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (sample : ℕ → X → A → Ω → X) (_hs : IsGenerativeModel M T μ sample),
          ENNReal.ofReal (1 - δ) ≤ μ {ω | ∀ s a,
            |syncQ M γ η Q0 (fun t s' a' => sample t s' a' ω) T s a - qStar M γ s a| ≤ ε} := by sorry

end TightQLearning
