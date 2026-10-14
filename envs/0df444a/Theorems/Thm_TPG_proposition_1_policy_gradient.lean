-- Prove2me | Theorems.Thm_TPG_proposition_1_policy_gradient
-- name    : TPG.proposition_1_policy_gradient
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:04:11.43454+00:00
-- url     : https://prove2.me/theorems/5321e2d3-830f-4583-93ca-adf55bf19b03
-- title:
--   Proposition 1 — the policy gradient $\nabla J(1/2)$ is the average $Q$-value difference
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   The **value function** is $J(\theta)=\frac1T\sum_{t<T}\mathbb E_\theta[Y_t]$, and the **$Q$-value** of action $z$ at time $t$ under the experimental policy $\pi_{1/2}$ is the expected cumulative reward from time $t$ to the end of the horizon given that action,
--
--   $$Q_{1/2}^{t}(z)=\sum_{u=t}^{T-1}\mathbb E_{1/2}[Y_u\mid Z_t=z].$$
--
--   **Proposition.** For every $T\ge1$, the function $J$ is differentiable at $\theta=1/2$ and
--
--   $$\nabla J(1/2)=\frac1T\sum_{t=0}^{T-1}\bigl(Q_{1/2}^{t}(1)-Q_{1/2}^{t}(0)\bigr).$$
--
--   This identifies the derivative of the policy value at the balanced design with a quantity that the untruncated estimator $\widehat\tau_T$ estimates without bias, and is the basis of the policy-gradient interpretation of the TPG estimator.
--
--   **Formalization Note** The $Q$-values do not depend on the state; they are expectations under the conditional law given the event $\{Z_t=z\}$, which has probability $1/2$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §4, pp. 13–14, Proposition 1, eqs. (6)–(7); proof in Appendix G.1, pp. 42–43.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem proposition_1_policy_gradient {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (M : ℝ) (hT : 0 < T) (hM : E.RewardBound M) :
    HasDerivAt (fun θ : ℝ => E.J T θ)
      ((1 / (T : ℝ)) * ∑ t : Fin T, (E.Q (1 / 2) T t true - E.Q (1 / 2) T t false))
      (1 / 2) := by sorry
end TPG
