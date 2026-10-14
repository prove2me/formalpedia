-- Prove2me | Theorems.Thm_TPG_untruncated_variance_bound
-- name    : TPG.untruncated_variance_bound
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:19:35.337605+00:00
-- url     : https://prove2.me/theorems/11c2e671-8173-4b76-979a-cc7a0a6d3f09
-- title:
--   Proposition 2, variance part — $\operatorname{Var}(\widehat\tau_T)\le2M^2(T+1)$ without mixing
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   Let $\widehat\tau_T=\frac1T\sum_{u<T}\bigl(\frac{\mathbf 1\{Z_u=1\}}{1/2}-\frac{\mathbf 1\{Z_u=0\}}{1/2}\bigr)\sum_{t=u}^{T-1}Y_t$ be the untruncated policy gradient estimator, computed from a trajectory generated under $\pi_{1/2}$.
--
--   **Statement.** For every $T\ge1$, with no mixing assumption,
--
--   $$\operatorname{Var}_{1/2}(\widehat\tau_T)\le2M^2(T+1).$$
--
--   This is the variance half of Proposition 2: without truncation the variance bound grows linearly in the horizon.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §4, p. 15, Proposition 2, eq. (8); proof at the end of Appendix G.2, p. 46.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem untruncated_variance_bound {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (M : ℝ) (hT : 0 < T) (hM : E.RewardBound M) :
    variance (tpgEst (1 / 2) T T) (E.expLaw T (1 / 2)) ≤ 2 * M ^ 2 * ((T : ℝ) + 1) := by sorry
end TPG
