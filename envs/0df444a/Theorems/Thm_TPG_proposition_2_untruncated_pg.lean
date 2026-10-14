-- Prove2me | Theorems.Thm_TPG_proposition_2_untruncated_pg
-- name    : TPG.proposition_2_untruncated_pg
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:05:12.786986+00:00
-- url     : https://prove2.me/theorems/714283ae-1061-4d2f-8c15-60a82d262829
-- title:
--   Proposition 2 — bias $O(T^2\delta^2M)$ and variance $\le 2M^2(T+1)$ of the untruncated PG estimator, without mixing
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   The **global average treatment effect** is $\tau=\frac1T\sum_{t<T}\bigl(\mathbb E_1[Y_t]-\mathbb E_0[Y_t]\bigr)$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$ with $\|f-g\|_{\mathrm{TV}}=\tfrac12\|f-g\|_1$, and $J(\theta)=\frac1T\sum_{t<T}\mathbb E_\theta[Y_t]$.
--
--   Let $\widehat\tau_T$ be the untruncated policy gradient estimator under $\pi_{1/2}$,
--
--   $$\widehat\tau_T=\frac1T\sum_{u=0}^{T-1}\Bigl(\frac{\mathbf 1\{Z_u=1\}}{1/2}-\frac{\mathbf 1\{Z_u=0\}}{1/2}\Bigr)\sum_{t=u}^{T-1}Y_t .$$
--
--   **Proposition.** No mixing assumption is imposed. There is an absolute constant $C>0$, not depending on the state space, the environment, $T$ or $M$, such that for every $T\ge1$:
--
--   1. $\bigl|\mathbb E_{1/2}[\widehat\tau_T]-\tau\bigr|\le C\,T^2\delta^2M$;
--   2. the same bound holds for the derivative of $J$ itself, $\bigl|J'(1/2)-\tau\bigr|\le C\,T^2\delta^2M$, hence for every unbiased estimator of $\nabla J(1/2)$;
--   3. $\operatorname{Var}_{1/2}(\widehat\tau_T)\le 2M^2(T+1)$.
--
--   This is the untruncated counterpart of Theorem 1: without mixing and truncation the bias bound grows quadratically and the variance bound linearly in the horizon.
--
--   **Formalization Note** The $O(\cdot)$ of the source is rendered by an existentially quantified constant chosen before the state space and the environment. Item 2 is stated for every real number $g$ that is a derivative of $J$ at $1/2$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §4, pp. 14–15, Proposition 2, eq. (8); proof in Appendix G.2, pp. 43–46.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem proposition_2_untruncated_pg :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
        (E : Env S) (T : ℕ) (M : ℝ),
        0 < T → E.RewardBound M →
          |(∫ ω, tpgEst (1 / 2) T T ω ∂(E.expLaw T (1 / 2))) - E.gate T|
              ≤ C * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M)
            ∧ (∀ g : ℝ, HasDerivAt (fun θ : ℝ => E.J T θ) g (1 / 2) →
                |g - E.gate T| ≤ C * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M))
            ∧ variance (tpgEst (1 / 2) T T) (E.expLaw T (1 / 2))
              ≤ 2 * M ^ 2 * ((T : ℝ) + 1) := by sorry
end TPG
