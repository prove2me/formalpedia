-- Prove2me | Theorems.Thm_TPG_theorem_1_bias_variance_bounds
-- name    : TPG.theorem_1_bias_variance_bounds
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:09:08.822502+00:00
-- url     : https://prove2.me/theorems/589c1075-bd23-4787-ae3e-e75ea894afc4
-- title:
--   Theorem 1 — bias and variance bounds for the TPG estimator
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Assumption 1 (mixing time)** with constant $\gamma\in(0,1)$: for every time $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$, $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, where $\|f-f'\|_{\mathrm{TV}}=\tfrac12\|f-f'\|_1$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   The **global average treatment effect** is $\tau=\frac1T\sum_{t<T}\bigl(\mathbb E_1[Y_t]-\mathbb E_0[Y_t]\bigr)$.
--
--   Let $\widehat\tau_k$ be the truncated policy gradient (TPG) estimator with truncation size $k$, computed from one trajectory generated under the experimental policy $\pi_{1/2}$:
--
--   $$\widehat\tau_k=\frac1T\sum_{u=0}^{T-1}\Bigl(\frac{\mathbf 1\{Z_u=1\}}{1/2}-\frac{\mathbf 1\{Z_u=0\}}{1/2}\Bigr)\sum_{t=u}^{\min(u+k,\,T-1)}Y_t .$$
--
--   **Theorem.** There are absolute constants $C_1,C_2>0$, not depending on the state space, the environment, or $T,k,\gamma,M$, such that under Assumption 1, for every $T\ge1$ and every truncation size $0\le k\le T$,
--
--   $$\bigl|\mathbb E_{1/2}[\widehat\tau_k]-\tau\bigr|\le C_1\Bigl(\frac{1-\gamma^k}{(1-\gamma)^2}\,\delta^2M+\frac{\gamma^k}{1-\gamma}\,\delta M\Bigr),$$
--
--   $$\operatorname{Var}_{1/2}(\widehat\tau_k)\le C_2\Bigl(\frac{(k+1)^2M^2}{T}+\frac{\gamma\,(k+1)M^2}{T(1-\gamma)}\Bigr).$$
--
--   The first term of the bias bound is the Taylor error of approximating a difference of policy values by a derivative, and the second is the mixing bias due to truncation. This is the main result of the source; it quantifies how the truncation size trades bias against variance.
--
--   **Formalization Note** The source states both bounds with $O(\cdot)$. The formal statement renders this with two existentially quantified constants chosen before the state space, the environment and all parameters.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §3, pp. 11–12, Theorem 1, eqs. (3)–(5); proof in Appendix F.1, pp. 37–41.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem theorem_1_bias_variance_bounds :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (S : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
        (E : Env S) (T k : ℕ) (γ M : ℝ),
        0 < T → k ≤ T → 0 < γ → γ < 1 → E.Mixing T γ → E.RewardBound M →
          |(∫ ω, tpgEst (1 / 2) T k ω ∂(E.expLaw T (1 / 2))) - E.gate T|
              ≤ C₁ * ((1 - γ ^ k) / (1 - γ) ^ 2 * (E.delta T) ^ 2 * M
                      + γ ^ k / (1 - γ) * E.delta T * M)
            ∧ variance (tpgEst (1 / 2) T k) (E.expLaw T (1 / 2))
              ≤ C₂ * (((k : ℝ) + 1) ^ 2 * M ^ 2 / (T : ℝ)
                      + γ * ((k : ℝ) + 1) * M ^ 2 / ((T : ℝ) * (1 - γ))) := by sorry
end TPG
