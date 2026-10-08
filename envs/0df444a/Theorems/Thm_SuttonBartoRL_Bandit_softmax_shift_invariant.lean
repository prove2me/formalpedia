-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_softmax_shift_invariant
-- name    : SuttonBartoRL.Bandit.softmax_shift_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:11.469424+00:00
-- url     : https://prove2.me/theorems/b36a9b3b-bab9-4428-be3b-2e7ba1d602de
-- title:
--   §2.8, p. 37 — soft-max probabilities are invariant under adding a constant to all preferences
-- statement:
--   Let $H \in \mathbb R^k$ be action preferences and $\pi_H$ the soft-max distribution $\pi_H(a) = e^{H(a)} / \sum_b e^{H(b)}$. For every real constant $c$ and every action $a$,
--
--   $$
--   \pi_{H + c}(a) = \pi_H(a),
--   $$
--
--   where $H + c$ adds $c$ to every preference.
--
--   Only the relative preference of one action over another matters for action selection; the book's example of adding $1000$ to all preferences is the case $c = 1000$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §2.8, sentence before Eq. (2.11), p. 37

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

namespace SuttonBartoRL.Bandit

theorem softmax_shift_invariant {k : ℕ} (H : Fin k → ℝ) (c : ℝ) (a : Fin k) :
    softmaxPolicy (fun b => H b + c) a = softmaxPolicy H a := by sorry

end SuttonBartoRL.Bandit
