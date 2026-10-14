-- Prove2me | Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
-- name    : TPG.isProbabilityMeasure_trajLaw
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:07:27.489131+00:00
-- url     : https://prove2.me/theorems/8a90b47a-d84c-49ee-9c7e-6fca7dc96f52
-- title:
--   The trajectory law is a probability measure
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** If $0\le q_t\le1$ for all $t$, then $\mathbb P_q$ is a probability measure on trajectories of length $T$; equivalently the path weights sum to one,
--
--   $$\sum_{x\in S^T}\ \sum_{z\in\{0,1\}^T}w_q(x,z)=1 .$$
--
--   Expectations, variances and conditional laws in the mission are taken with respect to this probability measure.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is implicit in §2.2, pp. 8–9 (the actions and the initial distribution determine the distribution of the process).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem isProbabilityMeasure_trajLaw {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) :
    IsProbabilityMeasure (E.trajLaw T q) := by sorry
end TPG
