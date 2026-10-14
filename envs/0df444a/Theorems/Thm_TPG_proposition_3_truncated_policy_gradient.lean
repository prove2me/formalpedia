-- Prove2me | Theorems.Thm_TPG_proposition_3_truncated_policy_gradient
-- name    : TPG.proposition_3_truncated_policy_gradient
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:06:20.536768+00:00
-- url     : https://prove2.me/theorems/ea649220-5e2c-4102-94bc-8b23ed513447
-- title:
--   Proposition 3 — the truncated policy gradient $\nabla J_k(1/2)$ is the average truncated $Q$-value difference
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   Fix a truncation size $k$. For a reward time $t$, the **hypothetical truncated policy** follows the experimental policy $\pi_{1/2}$ at the times $u<\max(0,t-k)$ and switches to $\pi_\theta$ at time $\max(0,t-k)$; $\mathcal L_\theta^{t,k}$ denotes the law of $Y_t$ under it. The **truncated policy value** and the **truncated $Q$-value** are
--
--   $$J_k(\theta)=\frac1T\sum_{t<T}\mathbb E_{\mathcal L_\theta^{t,k}}[Y_t],\qquad Q_{1/2}^{t,k}(z)=\sum_{u=t}^{\min(t+k,\,T-1)}\mathbb E_{1/2}[Y_u\mid Z_t=z].$$
--
--   **Proposition.** For every $T\ge1$ and $0\le k\le T$, the function $J_k$ is differentiable at $\theta=1/2$ and
--
--   $$\nabla J_k(1/2)=\frac1T\sum_{t=0}^{T-1}\bigl(Q_{1/2}^{t,k}(1)-Q_{1/2}^{t,k}(0)\bigr).$$
--
--   The right-hand side is the expectation of the TPG estimator $\widehat\tau_k$, so the estimator is unbiased for the truncated policy gradient.
--
--   **Formalization Note** In the formal definition the hypothetical policy keeps treatment probability $\theta$ after time $t$ as well, which does not affect the law of $Y_t$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §5 (Estimation via the truncated policy gradient estimator), pp. 15–16, Proposition 3, eqs. (9)–(10); proof in Appendix G.3, p. 46.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem proposition_3_truncated_policy_gradient {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (M : ℝ) (hT : 0 < T) (hk : k ≤ T) (hM : E.RewardBound M) :
    HasDerivAt (fun θ : ℝ => E.Jk T k θ)
      ((1 / (T : ℝ)) * ∑ t : Fin T, (E.Qk (1 / 2) T k t true - E.Qk (1 / 2) T k t false))
      (1 / 2) := by sorry
end TPG
