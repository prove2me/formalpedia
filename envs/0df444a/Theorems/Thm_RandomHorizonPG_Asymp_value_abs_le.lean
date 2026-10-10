-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_value_abs_le
-- name    : RandomHorizonPG.Asymp.value_abs_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:21.725568+00:00
-- url     : https://prove2.me/theorems/7fb7eca0-60e2-4cdb-b66a-fffc6a8f285e
-- title:
--   §3, p. 6 — |R| ≤ U_R implies |Q_π(s,a)| ≤ U_R/(1−γ) and |V_π(s)| ≤ U_R/(1−γ)
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$ and rewards bounded by $|R(s,a)|\le U_R$. Then for every stochastic policy $\nu$, every state $s$ and every action $a$,
--   $$
--   |Q_\nu(s,a)|\le\frac{U_R}{1-\gamma},\qquad |V_\nu(s)|\le\frac{U_R}{1-\gamma}.
--   $$
--   In particular $|J(\theta)|=|V_{\pi_\theta}(s_0)|\le U_R/(1-\gamma)$ for every parameter $\theta$.
--
--   This is the basic bound used throughout the paper: it makes $J$ bounded, bounds the $Q$-values entering the policy gradient, and controls the telescoping sums in the convergence proofs.
--
--   **Formalization Note** Stated for an arbitrary policy $\nu$ (a probability vector at each state), which contains the page's case $\nu=\pi_\theta$. $Q_\nu(s,a)=R(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\nu(s')$ is the published `QFunction`, equal to the page's $\mathbb E(\sum_t\gamma^tr_t\mid s_0=s,a_0=a)$. Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, §3, p. 6, the two displays after Assumption 3.1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning

/-- arXiv:1906.08383v3, §3, p. 6, displays after Assumption 3.1: if `|R(s,a)| ≤ U_R`, then for
every policy `ν`, `|Q_ν(s,a)| ≤ U_R/(1−γ)` and `|V_ν(s)| ≤ U_R/(1−γ)` (in particular
`|J(θ)| ≤ U_R/(1−γ)`). Stated for an arbitrary policy, which contains the page's `π_θ`. -/
theorem value_abs_le {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR : ℝ) (hP : IsTransitionKernel P)
    (hγ : 0 < γ ∧ γ < 1) (hR : ∀ s a, |R s a| ≤ UR) (ν : S → A → ℝ) (hν : IsPolicy ν) :
    (∀ s a, |QFunction ν P R γ s a| ≤ UR / (1 - γ)) ∧
      ∀ s, |PolicyValue ν P R γ s| ≤ UR / (1 - γ) := by sorry

end RandomHorizonPG.Asymp
