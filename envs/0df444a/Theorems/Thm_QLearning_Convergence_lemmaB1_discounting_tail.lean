-- Prove2me | Theorems.Thm_QLearning_Convergence_lemmaB1_discounting_tail
-- name    : QLearning.Convergence.lemmaB1_discounting_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:26.33555+00:00
-- url     : https://prove2.me/theorems/86c72e2e-a4e4-4e12-98e5-e67e3eb99bad
-- title:
--   Lemma B.1, p. 289 — the value of s actions with and without a continuation policy differ by at most γ^s ℛ/(1 − γ)
-- statement:
--   Let $(X,\mathfrak A,\mathcal R,P)$ be a finite controlled Markov process with $|\mathcal R_x(a)|\le\mathcal R$ for all $x,a$, and let $0<\gamma<1$. For a stationary policy $\pi$, a state $x$ and actions $a_1,\dots,a_s$, let $\bar Q(x,a_1,\dots,a_s)$ be the expected discounted reward of the $s$ actions with $0$ terminal reward and $\bar Q^\pi(x,a_1,\dots,a_s)$ the expected discounted reward of the same actions followed by $\pi$. Then
--   $$\bigl|\bar Q^\pi(x,a_1,\dots,a_s)-\bar Q(x,a_1,\dots,a_s)\bigr|\le\gamma^s\,\frac{\mathcal R}{1-\gamma}.$$
--
--   In particular the difference tends to $0$ as $s\to\infty$, uniformly in $x$, $\pi$ and the actions, which is the statement of Lemma B.1; the bound is the display in its proof, used in §3.2 to choose $s$.
--
--   **Formalization Note** The page prints strict inequalities $|V^\pi|<\mathcal R/(1-\gamma)$ and $|\delta|<\gamma^s\mathcal R/(1-\gamma)$; with $|r|\le\mathcal R$ only $\le$ holds (a constant reward $\mathcal R$ gives equality), so the bound is stated with $\le$. "Any arbitrary policy" is taken over stationary deterministic policies $\pi : X\to\mathfrak A$.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 289, Lemma B.1 and the display in its proof

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem lemmaB1_discounting_tail {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Rbar : ℝ) (hR : ∀ x a, |M.R x a| ≤ Rbar)
    (π : X → A) (x : X) (bs : List A) :
    |seqThenPolicy M γ π x bs - seqValue M γ x bs| ≤ γ ^ bs.length * (Rbar / (1 - γ)) := by sorry

end QLearning.Convergence
