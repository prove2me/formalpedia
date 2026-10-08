-- Prove2me | Theorems.Thm_QLearning_Convergence_lemmaB4_close_chains_close_values
-- name    : QLearning.Convergence.lemmaB4_close_chains_close_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:40.033355+00:00
-- url     : https://prove2.me/theorems/9f25c544-7e85-475f-a88e-07baf4145a52
-- title:
--   Lemma B.4, p. 291 — close rewards and transitions imply values of s actions within ηs(s + 1)/2
-- statement:
--   Let $(X,\mathfrak A,\mathcal R,P)$ be a finite controlled Markov process with $|\mathcal R_x(a)|\le\mathcal R$ for all $x,a$, where $\mathcal R>0$, and let $0<\gamma<1$. Let $P^i_{xy}[a]$, $i=1,\dots,s$ ($s\ge1$), be the transition matrices of $s$ Markov chains and $\mathcal R^i_x(a)$ reward functions, and let $\eta>0$. Suppose that for $i=1,\dots,s$ and all $x,a$,
--   $$\sum_y\bigl|P^i_{xy}[a]-P_{xy}[a]\bigr|<\frac{\eta}{\mathcal R},\qquad\bigl|\mathcal R^i_x(a)-\mathcal R_x(a)\bigr|<\eta.$$
--   Let $\bar Q'(x,a_1,\dots,a_s)$ be the expected discounted reward of the actions $a_1,\dots,a_s$ in the concatenated chain (step $i$ uses $P^i$ and $\mathcal R^i$) and $\bar Q(x,a_1,\dots,a_s)$ their value in the real process, both with $0$ terminal reward. Then for every $x$,
--   $$\bigl|\bar Q'(x,a_1,\dots,a_s)-\bar Q(x,a_1,\dots,a_s)\bigr|<\frac{s(s+1)}{2}\,\eta.$$
--
--   This converts the convergence of the ARP's one-step model (Lemma B.3) into closeness of the values of $s$ actions.
--
--   **Formalization Note** The page assumes each entry $P^i_{xy}[a]$ within $\eta/\mathcal R$ of $P_{xy}[a]$; with that hypothesis the printed constant $\eta s(s+1)/2$ fails once $|X|\ge4$ (e.g. $|X|=4$, $s=2$, $\gamma=0.99$ gives $0.396>3\eta=0.3$ at $\eta=0.1$). The statement uses closeness of rows in $\ell^1$, under which the printed constant holds and which is what the proof's recursion uses. The case $s=0$ is excluded because both values are $0$ there and the strict inequality fails; the page's "$i=1\dots s$" has $s\ge1$.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 291, Lemma B.4 and the last display of its proof

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem lemmaB4_close_chains_close_values {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Rbar : ℝ) (hRbar : 0 < Rbar) (hR : ∀ x a, |M.R x a| ≤ Rbar)
    (Ps : ℕ → X → A → X → ℝ) (Rs : ℕ → X → A → ℝ) (η : ℝ) (hη : 0 < η)
    (bs : List A) (hs : 1 ≤ bs.length)
    (hPs_nonneg : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a y, 0 ≤ Ps i x a y)
    (hPs_sum : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, ∑ y, Ps i x a y = 1)
    (hP : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, ∑ y, |Ps i x a y - M.P x a y| < η / Rbar)
    (hRs : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, |Rs i x a - M.R x a| < η) :
    ∀ x, |chainValue Ps Rs γ 1 x bs - seqValue M γ x bs|
      < (bs.length : ℝ) * (bs.length + 1) / 2 * η := by sorry

end QLearning.Convergence
