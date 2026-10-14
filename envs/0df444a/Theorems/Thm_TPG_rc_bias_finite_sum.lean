-- Prove2me | Theorems.Thm_TPG_rc_bias_finite_sum
-- name    : TPG.rc_bias_finite_sum
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:00:17.547005+00:00
-- url     : https://prove2.me/theorems/0047b788-ad3a-4f51-b59f-97a146fb83a5
-- title:
--   Finite-sum form of the bias bound for the reward-corrected estimator, valid for every $\gamma\ge0$
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Assumption 1 (mixing time)** with a constant $\gamma\ge0$ (not assumed smaller than one): for every time $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$, $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, where $\|f-f'\|_{\mathrm{TV}}=\tfrac12\|f-f'\|_1$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   The **global average treatment effect** is $\tau=\frac1T\sum_{t<T}\bigl(\mathbb E_1[Y_t]-\mathbb E_0[Y_t]\bigr)$.
--
--   Fix $\theta\in(0,1)$ and let $\widehat\tau^{\mathrm{RC}}_{\theta,k}=\frac1T\sum_{u<T}s_\theta(Z_u)\bigl[Y_u+\sum_{t=u+1}^{\min(u+k,T-1)}w_\theta(Z_t)Y_t\bigr]$ be the reward-corrected estimator, with $s_\theta(z)=\frac z\theta-\frac{1-z}{1-\theta}$ and $w_\theta(z)=\frac{(1-\theta)z}{\theta}+\frac{\theta(1-z)}{1-\theta}$, computed under $\pi_\theta$. Write $G_n(\gamma)=\sum_{j<n}\gamma^j$ and $\Psi_n(\gamma)=\sum_{j=0}^{n-2}(j+1)\gamma^j$ (so $\Psi_0=\Psi_1=0$), and for a reward time $t$ let $s_t=\max(0,t-k)$ be the start of its truncation window and $\ell_t=\min(t,k)=t-s_t$ its length.
--
--   **Lemma.** For every $T\ge1$ and $0\le k\le T$,
--
--   $$\Bigl|\mathbb E_\theta\bigl[\widehat\tau^{\mathrm{RC}}_{\theta,k}\bigr]-\tau\Bigr|\le\frac1T\sum_{t<T}\Bigl(2\delta M\,\gamma^{\ell_t}\,G_{s_t}(\gamma)+4\bigl[\theta^2+(1-\theta)^2\bigr]\delta^2M\,\Psi_{\ell_t}(\gamma)\Bigr).$$
--
--   Compared with the TPG estimator there is no first-order term in $\delta$. For $\gamma<1$ the bound implies the bias part of Proposition 6.
--
--   **Formalization Note** $t-k$ is a truncated subtraction of natural numbers.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the estimate obtained in Appendix G.6, pp. 48–51 (proof of Proposition 6) before the geometric sums are bounded by their limits.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem rc_bias_finite_sum {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 ≤ γ)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
      ≤ (1 / (T : ℝ)) * ∑ t : Fin T,
          (2 * E.delta T * M * γ ^ (min (t : ℕ) k) * (∑ j ∈ Finset.range ((t : ℕ) - k), γ ^ j)
            + 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi (min (t : ℕ) k) γ) := by sorry
end TPG
