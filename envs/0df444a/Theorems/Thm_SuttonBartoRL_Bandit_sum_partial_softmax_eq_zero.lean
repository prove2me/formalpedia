-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_sum_partial_softmax_eq_zero
-- name    : SuttonBartoRL.Bandit.sum_partial_softmax_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:37.714552+00:00
-- url     : https://prove2.me/theorems/d4f7fdc0-45ed-4453-b68a-a8f8152dcddc
-- title:
--   Box, p. 39 — the soft-max gradient sums to zero over the actions
-- statement:
--   Let $H \in \mathbb R^k$ be action preferences and $\pi$ the soft-max distribution (2.11). For every action $a$,
--
--   $$
--   \sum_x \frac{\partial \pi(x)}{\partial H(a)} = 0 .
--   $$
--
--   As $H(a)$ changes some probabilities go up and some go down, but their sum is always one. This is what allows a baseline to be subtracted from the rewards without changing the performance gradient.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "The Bandit Gradient Algorithm as Stochastic Gradient Ascent", p. 39

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem sum_partial_softmax_eq_zero {k : ℕ} (H : Fin k → ℝ) (a : Fin k) :
    ∑ x, partialDeriv (fun H' => softmaxPolicy H' x) H a = 0 := by sorry

end SuttonBartoRL.Bandit
