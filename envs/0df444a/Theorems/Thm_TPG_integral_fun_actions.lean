-- Prove2me | Theorems.Thm_TPG_integral_fun_actions
-- name    : TPG.integral_fun_actions
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:32:04.095883+00:00
-- url     : https://prove2.me/theorems/7f558eec-28be-410c-81b4-fbd16875900c
-- title:
--   Under the trajectory law the actions are independent Bernoulli variables
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$. For every function $g$ of the action path $(Z_t)_{t<T}\in\{0,1\}^T$,
--
--   $$\mathbb E_q\bigl[g(Z_0,\dots,Z_{T-1})\bigr]=\sum_{z\in\{0,1\}^T}\ \prod_{t<T}q_t^{\,z_t}(1-q_t)^{1-z_t}\ g(z).$$
--
--   So $Z_0,\dots,Z_{T-1}$ are independent with $Z_t\sim\mathrm{Bernoulli}(q_t)$, whatever the transition kernels are. The lemma is used to compute the moments of the inverse-propensity scores in the variance bounds.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it expresses the Bernoulli randomization design of §2.3, pp. 9–10 (the policy π_θ assigns treatment by i.i.d. Bernoulli(θ) variables, independently of all other randomness), for a time-varying sequence of probabilities.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_fun_actions {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (g : (Fin T → Bool) → ℝ) :
    ∫ ω, g (fun t => Z t ω) ∂(E.trajLaw T q)
      = ∑ z : Fin T → Bool, (∏ t : Fin T, if z t then q (t : ℕ) else 1 - q (t : ℕ)) * g z := by sorry
end TPG
