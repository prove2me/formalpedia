-- Prove2me | Theorems.Thm_TPG_integral_Y_trajLaw
-- name    : TPG.integral_Y_trajLaw
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:10:46.836242+00:00
-- url     : https://prove2.me/theorems/6b0b23aa-0616-4a0a-8a2e-f5b5b92cd055
-- title:
--   Expected reward in matrix form: $\mathbb E_q[Y_t]=\rho^\top P^0_{q_0}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t}$
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Suppose $0\le q_t\le1$ for all $t$ and $R([-M,M]\mid x,z)=1$ for all $x,z$. Then for every time $t<T$,
--
--   $$\mathbb E_q[Y_t]=\mu_q^t\,r_{q_t},\qquad \mu_q^t=\rho^\top P^0_{q_0}P^1_{q_1}\cdots P^{t-1}_{q_{t-1}},$$
--
--   where $P^s_\theta=\theta P^s_1+(1-\theta)P^s_0$, $r_\theta(x)=\theta\,r(x,1)+(1-\theta)\,r(x,0)$ and $r(x,z)=\int y\,R(dy\mid x,z)$.
--
--   Taking $q\equiv\theta$ gives the formula $\rho^\top P_\theta^{0\to t}r_\theta$ behind the value function $J$; other choices of $q$ give the hypothetical truncated policies and the laws conditioned on one action.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the identity E_{L_θ^t}[Y_t] = ρ^⊤ P_θ^{1→t} r_θ of Appendix G.1, p. 42, for a time-varying sequence of treatment probabilities.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_Y_trajLaw {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (M : ℝ) (hM : E.RewardBound M)
    (t : Fin T) :
    ∫ ω, Y t ω ∂(E.trajLaw T q) = dotProduct (E.stateVec q (t : ℕ)) (E.rMix (q (t : ℕ))) := by sorry
end TPG
