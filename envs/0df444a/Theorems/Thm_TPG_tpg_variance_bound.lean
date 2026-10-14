-- Prove2me | Theorems.Thm_TPG_tpg_variance_bound
-- name    : TPG.tpg_variance_bound
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:47:51.683501+00:00
-- url     : https://prove2.me/theorems/976b760f-fe93-469d-9bc8-1c952306c110
-- title:
--   Proposition 5, variance part — $\operatorname{Var}_\theta(\widehat\tau^{\mathrm{TPG}}_{\theta,k})\le\frac{M^2(k+1)}{Tp_\theta}\bigl(2k+3+\frac{4\gamma}{1-\gamma}\bigr)$
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Assumption 1 (mixing time)** with constant $\gamma\in(0,1)$: for every time $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$, $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, where $\|f-f'\|_{\mathrm{TV}}=\tfrac12\|f-f'\|_1$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   Fix $\theta\in(0,1)$ and let $\widehat\tau^{\mathrm{TPG}}_{\theta,k}=\frac1T\sum_{u<T}s_\theta(Z_u)\sum_{t=u}^{\min(u+k,T-1)}Y_t$, $s_\theta(z)=\frac z\theta-\frac{1-z}{1-\theta}$, computed from a trajectory generated under $\pi_\theta$; write $p_\theta=\theta(1-\theta)$.
--
--   **Statement.** Under Assumption 1, for every $T\ge1$ and $0\le k\le T$,
--
--   $$\operatorname{Var}_\theta\bigl(\widehat\tau^{\mathrm{TPG}}_{\theta,k}\bigr)\le\frac{M^2(k+1)}{T\,p_\theta}\Bigl(2k+3+\frac{4\gamma}{1-\gamma}\Bigr).$$
--
--   This is the variance half of Proposition 5; at $\theta=1/2$ it is the explicit form of the variance bound of Theorem 1.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix D, p. 32, Proposition 5, eq. (14); proof in Appendix G.5 following the variance bound of Appendix F.1, pp. 40–41, eqs. (36)–(38).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem tpg_variance_bound {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    variance (tpgEst θ T k) (E.expLaw T θ)
      ≤ M ^ 2 * ((k : ℝ) + 1) / ((T : ℝ) * (θ * (1 - θ)))
          * (2 * (k : ℝ) + 3 + 4 * γ / (1 - γ)) := by sorry
end TPG
