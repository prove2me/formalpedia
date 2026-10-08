-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_softmax_partial_deriv
-- name    : SuttonBartoRL.Bandit.softmax_partial_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:32.61399+00:00
-- url     : https://prove2.me/theorems/6bb19d5d-354a-4826-9c53-5429cfbcb5fe
-- title:
--   Box, p. 40 — the soft-max derivative $\partial\pi(x)/\partial H(a) = \pi(x)(\mathbb 1_{a=x} - \pi(a))$
-- statement:
--   Let $H \in \mathbb R^k$ be action preferences and $\pi$ the soft-max distribution (2.11). For all actions $x$ and $a$, the function $h \mapsto \pi(x)$ obtained by varying only the $a$-th preference is differentiable at $h = H(a)$, with
--
--   $$
--   \frac{\partial \pi(x)}{\partial H(a)} = \pi(x)\bigl(\mathbb 1_{a=x} - \pi(a)\bigr),
--   $$
--
--   where $\mathbb 1_{a=x}$ is $1$ if $a = x$ and $0$ otherwise.
--
--   This is the last step of the box showing that the gradient bandit algorithm is stochastic gradient ascent: it converts the performance gradient into an expectation of a quantity that can be sampled.
--
--   **Formalization Note** Stated with `HasDerivAt`, so it asserts differentiability as well as the value.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "The Bandit Gradient Algorithm as Stochastic Gradient Ascent", p. 40

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem softmax_partial_deriv {k : ℕ} (H : Fin k → ℝ) (x a : Fin k) :
    HasDerivAt (fun h => softmaxPolicy (Function.update H a h) x)
      (softmaxPolicy H x * ((if a = x then 1 else 0) - softmaxPolicy H a)) (H a) := by sorry

end SuttonBartoRL.Bandit
