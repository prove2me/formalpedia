-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_gradient_bandit_expected_update
-- name    : SuttonBartoRL.Bandit.gradient_bandit_expected_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:52.502999+00:00
-- url     : https://prove2.me/theorems/40f38d80-d784-4290-9e53-351889fea2a0
-- title:
--   Box, pp. 38–40 — the gradient bandit algorithm is stochastic gradient ascent: its expected update is the gradient step (2.13)
-- statement:
--   Consider a $k$-armed bandit in which action $x$ yields rewards with probability distribution $\nu_x$ on $\mathbb R$, integrable with mean $q_*(x)$. Let $H \in \mathbb R^k$ be the current action preferences, $\pi$ the soft-max distribution (2.11), $\alpha > 0$ a step size and $B \in \mathbb R$ a baseline that does not depend on the selected action. Draw $A \sim \pi$ and, given $A = x$, a reward $R \sim \nu_x$, and let $H'$ be the preferences after one step of the gradient bandit algorithm (2.12) with baseline $B$. Then for every action $a$,
--
--   $$
--   \mathbb E\bigl[H'(a)\bigr] = H(a) + \alpha\, \frac{\partial\, \mathbb E[R]}{\partial H(a)},
--   \qquad \mathbb E[R] = \sum_x \pi(x)\, q_*(x),
--   $$
--
--   that is, the update (2.12) equals the exact gradient-ascent step (2.13) on the expected reward in expected value, and the gradient bandit algorithm is an instance of stochastic gradient ascent.
--
--   The right-hand side cannot be computed without knowing $q_*$, while the left-hand side is the mean of a quantity computed from one sampled action and reward; this is what makes the algorithm implementable. The identity holds for every baseline independent of the action, which is why the baseline affects the variance of the update but not its mean.
--
--   **Formalization Note** The expectation is over the mixture $\sum_x \pi(x)\,\nu_x$ of $(A, R)$; integrability of rewards is a hypothesis. The baseline is a fixed real $B$, which covers the book's $B_t = \bar R_t$ (the average of rewards before time $t$) once one conditions on the past. It does not cover a baseline that includes the current reward $R_t$, as in the chapter's experiments (footnote 1, p. 37), since that depends on $A_t$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "The Bandit Gradient Algorithm as Stochastic Gradient Ascent", Eq. (2.13), pp. 38–40, with Eqs. (2.11)–(2.12), p. 37

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem gradient_bandit_expected_update {k : ℕ} (α : ℝ) (hα : 0 < α) (H qstar : Fin k → ℝ)
    (ν : Fin k → MeasureTheory.Measure ℝ) [∀ x, MeasureTheory.IsProbabilityMeasure (ν x)]
    (hint : ∀ x, MeasureTheory.Integrable (fun r : ℝ => r) (ν x))
    (hmean : ∀ x, ∫ r, r ∂(ν x) = qstar x) (B : ℝ) (a : Fin k) :
    ∑ x, softmaxPolicy H x * ∫ r, gradientBanditUpdate α H x r B a ∂(ν x)
      = H a + α * partialDeriv (expectedReward qstar) H a := by sorry

end SuttonBartoRL.Bandit
