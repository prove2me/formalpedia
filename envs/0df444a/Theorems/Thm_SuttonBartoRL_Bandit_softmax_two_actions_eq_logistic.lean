-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_softmax_two_actions_eq_logistic
-- name    : SuttonBartoRL.Bandit.softmax_two_actions_eq_logistic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:36.344571+00:00
-- url     : https://prove2.me/theorems/4b18e42e-3610-4c19-93a0-a68ce41b950c
-- title:
--   Exercise 2.9 — with two actions the soft-max is the logistic (sigmoid) function
-- statement:
--   Let there be two actions with preferences $H(1), H(2)$, and let $\sigma(x) = 1/(1 + e^{-x})$ be the logistic (sigmoid) function. Then the soft-max probabilities are
--
--   $$
--   \pi(1) = \sigma\bigl(H(1) - H(2)\bigr), \qquad \pi(2) = \sigma\bigl(H(2) - H(1)\bigr).
--   $$
--
--   This identifies the two-action gradient bandit policy with logistic regression on the preference difference.
--
--   **Formalization Note** The book gives no solution; "the soft-max distribution is the same as that given by the logistic function" is read as the two displayed equalities. The two actions are `0` and `1` in `Fin 2`, and $\sigma$ is written out explicitly.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 2.9, p. 37 (the book gives no solution)

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem softmax_two_actions_eq_logistic (H : Fin 2 → ℝ) :
    softmaxPolicy H 0 = 1 / (1 + Real.exp (-(H 0 - H 1))) ∧
      softmaxPolicy H 1 = 1 / (1 + Real.exp (-(H 1 - H 0))) := by sorry

end SuttonBartoRL.Bandit
