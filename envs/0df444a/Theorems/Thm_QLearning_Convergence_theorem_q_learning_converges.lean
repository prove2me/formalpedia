-- Prove2me | Theorems.Thm_QLearning_Convergence_theorem_q_learning_converges
-- name    : QLearning.Convergence.theorem_q_learning_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:32.04079+00:00
-- url     : https://prove2.me/theorems/ae845100-339c-4958-b98c-9077fcd5f747
-- title:
--   Theorem, p. 282 — with |r_n| ≤ ℛ, 0 ≤ α_n < 1 and (3), Q_n(x, a) → Q*(x, a) for all x, a with probability 1
-- statement:
--   Let $(X,\mathfrak A,\mathcal R,P)$ be a finite controlled Markov process with a nonempty action set, let $0<\gamma<1$, and let $Q^*$ be its optimal action-value function, i.e. the solution of
--   $$Q^*(x,a)=\mathcal R_x(a)+\gamma\sum_y P_{xy}[a]\max_b Q^*(y,b).$$
--   On a probability space with a filtration $(\mathcal F_n)$, let the episodes $(x_n,a_n,y_n,r_n,\alpha_n)_{n\ge1}$ satisfy:
--
--   1. the state $x_n$, action $a_n$ and learning rate $\alpha_n$ of episode $n$ are $\mathcal F_{n-1}$-measurable, and the outcome $(y_n,r_n)$ is $\mathcal F_n$-measurable;
--   2. $\Pr[y_n=y\mid\mathcal F_{n-1}]=P_{x_ny}[a_n]$ for every $y$, and $\mathbb E[r_n\mid\mathcal F_{n-1}]=\mathcal R_{x_n}(a_n)$;
--   3. the rewards are bounded, $|r_n|\le\mathcal R$, and the learning rates satisfy $0\le\alpha_n<1$;
--   4. with probability $1$, for every pair $(x,a)$, writing $n^i(x,a)$ for the episode of the $i$-th visit to $(x,a)$,
--   $$\sum_{i=1}^\infty\alpha_{n^i(x,a)}=\infty,\qquad\sum_{i=1}^\infty\bigl[\alpha_{n^i(x,a)}\bigr]^2<\infty.\tag{3}$$
--
--   Let $Q_n$ be the Q-learning iterates (1) from given initial values $Q_0$. Then with probability $1$,
--   $$Q_n(x,a)\to Q^*(x,a)\quad\text{as }n\to\infty,\ \text{for all }x,a.$$
--
--   This is the convergence theorem of tabular Q-learning: an agent that tries every action in every state infinitely often, with suitably decreasing learning rates, learns the optimal action values without a model of the process.
--
--   **Formalization Note** The paper states the probability model only in words. The statement pins the reading under which the theorem is known to hold (Tsitsiklis 1994; Jaakkola, Jordan and Singh 1994): the agent chooses the next state, action and learning rate from the past (predictable choices), the next state has law $P_{x_n\cdot}[a_n]$ and the reward has mean $\mathcal R_{x_n}(a_n)$ given the past. Episodes with states, actions and learning rates fixed in advance and independent outcomes are a special case. Condition (3) is written as a sum over episodes of the learning rate charged to $(x,a)$, which equals the sum over visits and forces infinitely many visits. Lean index $n$ is the paper's episode $n$; index $0$ of the data is unused and $Q_0$ is deterministic.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 282, Theorem; proof §3 and Appendix, pp. 282–291

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem theorem_q_learning_converges {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qstar : X → A → ℝ) (hQ : IsOptimalQ M γ Qstar) (Q0 : X → A → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀ n, Measurable[ℱ n] (xs (n + 1)))
    (has : ∀ n, Measurable[ℱ n] (as (n + 1)))
    (hαs : ∀ n, Measurable[ℱ n] (αs (n + 1)))
    (hys : ∀ n, Measurable[ℱ (n + 1)] (ys (n + 1)))
    (hrs : ∀ n, Measurable[ℱ (n + 1)] (rs (n + 1)))
    (htrans : ∀ n y, μ[fun ω => if ys (n + 1) ω = y then (1 : ℝ) else 0 | ℱ n]
      =ᵐ[μ] fun ω => M.P (xs (n + 1) ω) (as (n + 1) ω) y)
    (hrew : ∀ n, μ[rs (n + 1) | ℱ n] =ᵐ[μ] fun ω => M.R (xs (n + 1) ω) (as (n + 1) ω))
    (Rbar : ℝ) (hbdd : ∀ n ω, |rs n ω| ≤ Rbar)
    (hα : ∀ n ω, 0 ≤ αs n ω ∧ αs n ω < 1)
    (h3 : ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1)) atTop atTop ∧
      Summable (fun n =>
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun n => qIter γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
          (fun k => rs k ω) (fun k => αs k ω) n x a) atTop (𝓝 (Qstar x a)) := by sorry

end QLearning.Convergence
