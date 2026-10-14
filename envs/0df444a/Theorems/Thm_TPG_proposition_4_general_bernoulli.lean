-- Prove2me | Theorems.Thm_TPG_proposition_4_general_bernoulli
-- name    : TPG.proposition_4_general_bernoulli
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:06:52.786052+00:00
-- url     : https://prove2.me/theorems/1eb2c148-7421-4295-8419-40acd6c0d562
-- title:
--   Proposition 4 — TPG under general Bernoulli randomization is unbiased for the truncated policy gradient
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   Fix an experimental allocation $\theta\in(0,1)$ and a truncation size $k$. With the score $s_\theta(z)=\dfrac{z}{\theta}-\dfrac{1-z}{1-\theta}$, the TPG estimator and the truncated $Q$-values under $\pi_\theta$ are
--
--   $$\widehat\tau^{\mathrm{TPG}}_{\theta,k}=\frac1T\sum_{u=0}^{T-1}s_\theta(Z_u)\sum_{t=u}^{\min(u+k,\,T-1)}Y_t,\qquad Q_\theta^{u,k}(z)=\sum_{t=u}^{\min(u+k,\,T-1)}\mathbb E_\theta[Y_t\mid Z_u=z].$$
--
--   Write $P_q^t=qP_1^t+(1-q)P_0^t$, $P_q^{a\to b}=P_q^{a}\cdots P_q^{b-1}$, $r_q(x)=q\,r(x,1)+(1-q)\,r(x,0)$ with $r(x,z)=\int y\,R(dy\mid x,z)$, and $\mu_q^t=\rho^\top P_q^{0\to t}$. The **hypothetical truncated policy value** is, with $a_t=\max(0,t-k)$,
--
--   $$J_{k,\theta}(q)=\frac1T\sum_{t<T}\mu_\theta^{a_t}\,P_q^{a_t\to t}\,r_q ,$$
--
--   and $J(q)=\frac1T\sum_{t<T}\mathbb E_q[Y_t]$ is the value function.
--
--   **Proposition.** For every $T\ge1$, $0\le k\le T$ and $\theta\in(0,1)$:
--
--   1. $\displaystyle \mathbb E_\theta\bigl[\widehat\tau^{\mathrm{TPG}}_{\theta,k}\bigr]=\frac1T\sum_{u=0}^{T-1}\bigl[Q_\theta^{u,k}(1)-Q_\theta^{u,k}(0)\bigr]$;
--   2. $q\mapsto J_{k,\theta}(q)$ is differentiable at $q=\theta$ with derivative equal to the same quantity, $\displaystyle\frac{\partial}{\partial q}J_{k,\theta}(q)\Big|_{q=\theta}=\frac1T\sum_{u=0}^{T-1}\bigl[Q_\theta^{u,k}(1)-Q_\theta^{u,k}(0)\bigr]$;
--   3. for $k=T$, $J_{T,\theta}(q)=J(q)$ for all $q\in[0,1]$;
--   4. $J$ is differentiable at $\theta$ and $\mathbb E_\theta\bigl[\widehat\tau^{\mathrm{TPG}}_{\theta,T}\bigr]=J'(\theta)$.
--
--   This extends the policy-gradient interpretation of the main text (Propositions 1 and 3) from $\theta=1/2$ to every interior experimental allocation.
--
--   **Formalization Note** $J_{k,\theta}$ is defined by the matrix expression of the source, with $t-k$ a truncated subtraction; item 3 is stated on $[0,1]$, where $\pi_q$ is a policy.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix D, pp. 31–32, Proposition 4, eqs. (11)–(12); proof in Appendix G.4, p. 46.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem proposition_4_general_bernoulli {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : E.RewardBound M) :
    (∫ ω, tpgEst θ T k ω ∂(E.expLaw T θ)
        = (1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false))
      ∧ HasDerivAt (fun q : ℝ => E.JkGen T k θ q)
          ((1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false)) θ
      ∧ (∀ q : ℝ, 0 ≤ q → q ≤ 1 → E.JkGen T T θ q = E.J T q)
      ∧ HasDerivAt (fun q : ℝ => E.J T q) (∫ ω, tpgEst θ T T ω ∂(E.expLaw T θ)) θ := by sorry
end TPG
