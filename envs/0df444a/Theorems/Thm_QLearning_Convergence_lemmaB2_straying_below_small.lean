-- Prove2me | Theorems.Thm_QLearning_Convergence_lemmaB2_straying_below_small
-- name    : QLearning.Convergence.lemmaB2_straying_below_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:27.93146+00:00
-- url     : https://prove2.me/theorems/cb7a4b53-fcc9-49a8-a7e3-462ca1c635b6
-- title:
--   Lemma B.2, p. 289 — from a high enough level, the ARP strays below level l within s actions with arbitrarily small probability
-- statement:
--   Fix a sequence of episodes $(x_n,a_n,y_n)_{n\ge1}$ with learning rates $0\le\alpha_n<1$ such that $\sum_i\alpha_{n^i(x,a)}=\infty$ for every pair $(x,a)$, and consider the action-replay process built from it. Then for every level $l$, every number of actions $s$ and every $\varepsilon>0$ there is a level $h$ such that for every $n>h$, every state $x$ and every sequence of $s$ actions $a_1,\dots,a_s$,
--   $$\Pr\bigl[\text{the ARP started at }\langle x,n\rangle\text{ is absorbed or below level }l\text{ after }a_1,\dots,a_s\bigr]<\varepsilon.$$
--
--   This is what lets the proof treat the ARP, started high enough, as running for $s$ steps on decks that are long enough for its transition model to be close to the real one.
--
--   **Formalization Note** Actions are a fixed (open-loop) list, as in "after taking $s$ actions". Levels never increase, so "below $l$ after $s$ actions" and "below $l$ at some point within $s$ actions" coincide; absorption counts as straying. Only the first half of condition (3) is assumed, which is what the proof uses.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 289, Lemma B.2

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem lemmaB2_straying_below_small {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (αs : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ αs n ∧ αs n < 1)
    (hvis : ∀ x a, Tendsto (fun N => ∑ n ∈ Finset.range N, visitRate xs as αs x a (n + 1))
      atTop atTop) :
    ∀ (l s : ℕ) (ε : ℝ), 0 < ε → ∃ h : ℕ, ∀ n, h < n → ∀ (x : X) (bs : List A),
      bs.length = s → 1 - arpProbAbove xs as ys αs l bs x n < ε := by sorry

end QLearning.Convergence
