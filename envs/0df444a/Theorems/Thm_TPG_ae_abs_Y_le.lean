-- Prove2me | Theorems.Thm_TPG_ae_abs_Y_le
-- name    : TPG.ae_abs_Y_le
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:52:37.333399+00:00
-- url     : https://prove2.me/theorems/f9200d5a-5222-40f2-9aab-b495a74f4b69
-- title:
--   Rewards are almost surely bounded under the trajectory law
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** If $R([-M,M]\mid x,z)=1$ for all $x,z$, then for every horizon $T$ and every real sequence $q$,
--
--   $$\mathbb P_q\bigl(|Y_t|\le M\ \text{for all }t<T\bigr)\ \text{has full measure},$$
--
--   i.e. almost surely $|Y_t|\le M$ for every $t$.
--
--   The lemma lets bounded-reward arguments be applied to functions of the observed rewards, which are bounded only almost surely.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it transfers the boundedness assumption R([-M,M] | x,z) = 1 of §2.2, p. 9, to the trajectory.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem ae_abs_Y_le {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (M : ℝ) (hM : E.RewardBound M) :
    ∀ᵐ ω ∂(E.trajLaw T q), ∀ t : Fin T, |Y t ω| ≤ M := by sorry
end TPG
