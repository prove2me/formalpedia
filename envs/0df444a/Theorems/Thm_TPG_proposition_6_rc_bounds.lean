-- Prove2me | Theorems.Thm_TPG_proposition_6_rc_bounds
-- name    : TPG.proposition_6_rc_bounds
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:08:00.655397+00:00
-- url     : https://prove2.me/theorems/ae3fb00f-5df6-41bf-98c6-3b1ef740382a
-- title:
--   Proposition 6 — bias and variance bounds for the reward-corrected (RC) estimator
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Assumption 1 (mixing time)** with constant $\gamma\in(0,1)$: for every time $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$, $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, where $\|f-f'\|_{\mathrm{TV}}=\tfrac12\|f-f'\|_1$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   The **global average treatment effect** is $\tau=\frac1T\sum_{t<T}\bigl(\mathbb E_1[Y_t]-\mathbb E_0[Y_t]\bigr)$.
--
--   Fix $\theta\in(0,1)$. With the score $s_\theta(z)=\dfrac z\theta-\dfrac{1-z}{1-\theta}$ and the additional importance weight $w_\theta(z)=\dfrac{(1-\theta)z}{\theta}+\dfrac{\theta(1-z)}{1-\theta}$, the **reward-corrected estimator** with truncation size $k$, computed from a trajectory generated under $\pi_\theta$, is
--
--   $$\widehat\tau^{\mathrm{RC}}_{\theta,k}=\frac1T\sum_{u=0}^{T-1}s_\theta(Z_u)\Bigl[Y_u+\sum_{t=u+1}^{\min(u+k,\,T-1)}w_\theta(Z_t)\,Y_t\Bigr].$$
--
--   Write $p_\theta=\theta(1-\theta)$, $c_\theta=1+\dfrac{(1-2\theta)^2}{p_\theta}$ and $\Psi_k(\gamma)=\sum_{j=0}^{k-2}(j+1)\gamma^j$ (so $\Psi_0=\Psi_1=0$).
--
--   **Proposition.** Under Assumption 1, for every $T\ge1$, $\theta\in(0,1)$ and integer $0\le k\le T$:
--
--   $$\Bigl|\mathbb E_\theta\bigl[\widehat\tau^{\mathrm{RC}}_{\theta,k}\bigr]-\tau\Bigr|\le\frac{2\delta M\gamma^k}{1-\gamma}+4\bigl[\theta^2+(1-\theta)^2\bigr]\delta^2M\,\Psi_k(\gamma),$$
--
--   $$\operatorname{Var}_\theta\bigl(\widehat\tau^{\mathrm{RC}}_{\theta,k}\bigr)\le\frac{M^2}{T\,p_\theta}\,(1+k\,c_\theta)\Bigl(2k+3+\frac{4\gamma}{1-\gamma}\Bigr).$$
--
--   When $k\ge T-1$, the first term of the bias bound can be omitted.
--
--   Compared with Proposition 5, the reward correction removes the first-order term in $\delta$ that appears away from balanced randomization, at the cost of a larger variance bound. At $\theta=1/2$ the two estimators coincide.
--
--   **Formalization Note** The remark on $k\ge T-1$ is the third conjunct of the formal statement, under the hypothesis $T\le k+1$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix E.1, p. 33 (RC estimator) and Appendix E.3, p. 36, Proposition 6, eqs. (22)–(23); proof in Appendix G.6, pp. 48–51.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem proposition_6_rc_bounds {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
        ≤ 2 * E.delta T * M * γ ^ k / (1 - γ)
          + 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ
      ∧ variance (rcEst θ T k) (E.expLaw T θ)
        ≤ M ^ 2 / ((T : ℝ) * (θ * (1 - θ)))
            * (1 + (k : ℝ) * (1 + (1 - 2 * θ) ^ 2 / (θ * (1 - θ))))
            * (2 * (k : ℝ) + 3 + 4 * γ / (1 - γ))
      ∧ (T ≤ k + 1 →
          |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
            ≤ 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ) := by sorry
end TPG
