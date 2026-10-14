-- Prove2me | Theorems.Thm_TPG_gate_eq_meanReward
-- name    : TPG.gate_eq_meanReward
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:21:27.379863+00:00
-- url     : https://prove2.me/theorems/83140493-ce87-4ddd-9c10-3083af1df552
-- title:
--   The GATE in matrix form: $\tau=\frac1T\sum_t\bigl(\rho^\top P_1^{0\to t}r_1-\rho^\top P_0^{0\to t}r_0\bigr)$
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** If $R([-M,M]\mid x,z)=1$ for all $x,z$, then the global average treatment effect satisfies
--
--   $$\tau=\frac1T\sum_{t<T}\bigl(m_t(\mathbf 1)-m_t(\mathbf 0)\bigr),\qquad m_t(q)=\rho^\top P^0_{q_0}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t},$$
--
--   where $\mathbf 1$ and $\mathbf 0$ are the constant sequences, so that $m_t(\mathbf 1)=\rho^\top P_1^0\cdots P_1^{t-1}r_1$ and $m_t(\mathbf 0)=\rho^\top P_0^0\cdots P_0^{t-1}r_0$.
--
--   This is the estimand in the form compared with the expectation of the estimators in the bias bounds.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the identity E_{L_1^t}[Y_t] = ρ^⊤ P_1^{1→t} r_1 of eq. (30), p. 39 (Appendix F.1), averaged over the horizon.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem gate_eq_meanReward {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (M : ℝ) (hM : E.RewardBound M) :
    E.gate T
      = (1 / (T : ℝ)) * ∑ t : Fin T,
          (E.meanReward (fun _ => 1) (t : ℕ) - E.meanReward (fun _ => 0) (t : ℕ)) := by sorry
end TPG
