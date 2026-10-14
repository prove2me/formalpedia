-- Prove2me | Theorems.Thm_TPG_integral_tpgEst
-- name    : TPG.integral_tpgEst
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:21:55.901509+00:00
-- url     : https://prove2.me/theorems/9c991398-1ca0-4727-8b95-e94f5bdf710b
-- title:
--   Expectation of the TPG estimator in matrix form
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   Let $\widehat\tau^{\mathrm{TPG}}_{\theta,k}=\frac1T\sum_{u<T}s_\theta(Z_u)\sum_{t=u}^{\min(u+k,T-1)}Y_t$ with $s_\theta(z)=\frac z\theta-\frac{1-z}{1-\theta}$, and let $m_t(q)=\rho^\top P^0_{q_0}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t}$ be the expected reward at time $t$ under the randomization sequence $q$.
--
--   **Lemma.** If $0<\theta<1$ and $R([-M,M]\mid x,z)=1$ for all $x,z$, then
--
--   $$\mathbb E_\theta\bigl[\widehat\tau^{\mathrm{TPG}}_{\theta,k}\bigr]=\frac1T\sum_{u<T}\ \sum_{t=u}^{\min(u+k,\,T-1)}\Bigl(m_t\bigl(\theta^{u\to1}\bigr)-m_t\bigl(\theta^{u\to0}\bigr)\Bigr),$$
--
--   where $\theta^{u\to b}$ is the constant sequence $\theta$ with the entry at time $u$ replaced by $b$.
--
--   Each term is the effect on the expected reward at time $t$ of forcing the action at time $u$; the lemma reduces the bias analysis of the estimator to matrix algebra.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the first line of the display ending in eq. (20), p. 34 (Appendix E.2), E_θ[τ̂^TPG_{θ,k}] = (1/T) Σ_t [μ_θ^t (r_1 − r_0) + A^t_{θ,k} r_θ], written with one-coordinate changes of the randomization sequence.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_tpgEst {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : E.RewardBound M) :
    ∫ ω, tpgEst θ T k ω ∂(E.expLaw T θ)
      = (1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
          if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
            (E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ)
              - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ))
          else 0 := by sorry
end TPG
