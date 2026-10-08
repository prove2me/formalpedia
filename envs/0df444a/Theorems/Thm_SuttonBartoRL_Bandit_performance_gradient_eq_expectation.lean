-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_performance_gradient_eq_expectation
-- name    : SuttonBartoRL.Bandit.performance_gradient_eq_expectation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:53.480284+00:00
-- url     : https://prove2.me/theorems/c8118741-8b71-463f-acd2-c8c2a43e0f70
-- title:
--   Box, p. 39 — the performance gradient is $\mathbb E[(R_t - B_t)(\mathbb 1_{a=A_t} - \pi_t(a))]$
-- statement:
--   Let $H \in \mathbb R^k$ be action preferences, $\pi$ the soft-max distribution (2.11), and for each action $x$ let $\nu_x$ be a probability distribution on $\mathbb R$ (the reward distribution of $x$) with finite mean $q_*(x) = \int r\, d\nu_x(r)$. Let $B \in \mathbb R$ be any baseline not depending on the action. The action $A$ is drawn from $\pi$ and, given $A = x$, the reward $R$ is drawn from $\nu_x$. Then for every action $a$,
--
--   $$
--   \frac{\partial\, \mathbb E[R]}{\partial H(a)}
--   = \mathbb E\bigl[(R - B)(\mathbb 1_{a=A} - \pi(a))\bigr]
--   = \sum_x \pi(x) \int (r - B)\bigl(\mathbb 1_{a=x} - \pi(a)\bigr)\, d\nu_x(r),
--   $$
--
--   where $\mathbb E[R] = \sum_x \pi(x) q_*(x)$ is the expected reward as a function of $H$.
--
--   This writes the exact performance gradient as the expectation of a quantity observable after one step of the bandit, which is the core of the stochastic-gradient interpretation.
--
--   **Formalization Note** The joint law of $(A, R)$ is encoded by the mixture $\sum_x \pi(x)\,\nu_x$; integrability of the reward under each $\nu_x$ is a hypothesis (otherwise the Bochner integral would be $0$). The book's $B_t = \bar R_t$ is covered as one choice of the constant $B$ (conditioning on the past).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "The Bandit Gradient Algorithm as Stochastic Gradient Ascent", p. 39

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem performance_gradient_eq_expectation {k : ℕ} (H qstar : Fin k → ℝ)
    (ν : Fin k → MeasureTheory.Measure ℝ) [∀ x, MeasureTheory.IsProbabilityMeasure (ν x)]
    (hint : ∀ x, MeasureTheory.Integrable (fun r : ℝ => r) (ν x))
    (hmean : ∀ x, ∫ r, r ∂(ν x) = qstar x) (B : ℝ) (a : Fin k) :
    partialDeriv (expectedReward qstar) H a
      = ∑ x, softmaxPolicy H x *
          ∫ r, (r - B) * ((if a = x then 1 else 0) - softmaxPolicy H a) ∂(ν x) := by sorry

end SuttonBartoRL.Bandit
