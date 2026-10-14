-- Prove2me | Theorems.Thm_TPG_trajLaw_eq_sum_map
-- name    : TPG.trajLaw_eq_sum_map
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:48:29.116056+00:00
-- url     : https://prove2.me/theorems/9796532d-b624-4852-998b-7b64f5a45f1f
-- title:
--   The trajectory law is a finite mixture of product reward laws along state–action paths
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** For every horizon $T$ and every real sequence $q$, the trajectory law is the finite mixture
--
--   $$\mathbb P_q=\sum_{x\in S^T}\ \sum_{z\in\{0,1\}^T}\ \max\{w_q(x,z),0\}\cdot\bigl(\iota_{x,z}\bigr)_{\#}\Bigl(\bigotimes_{t<T}R(\cdot\mid x_t,z_t)\Bigr),$$
--
--   where
--
--   $$w_q(x,z)=\rho(x_0)\prod_{s+1<T}P^s_{z_s}(x_s,x_{s+1})\prod_{t<T}q_t^{\,z_t}(1-q_t)^{1-z_t}$$
--
--   is the path weight and $\iota_{x,z}(y)=(x_t,z_t,y_t)_{t<T}$ inserts a reward vector $y\in\mathbb R^T$ into the trajectory with state path $x$ and action path $z$.
--
--   This is the working form of the definition: conditionally on the state and action paths, the rewards are independent with the prescribed laws. Integrals against the trajectory law reduce through it to finite sums of integrals against product measures.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it restates the definition of the process in §2.2, pp. 8–9 (Markov process; rewards conditionally independent given states and actions).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem trajLaw_eq_sum_map {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) :
    E.trajLaw T q
      = ∑ p : (Fin T → S) × (Fin T → Bool),
          ENNReal.ofReal (E.pathWeight T q p.1 p.2) •
            (E.rewardLaw p.1 p.2).map (embedPath p.1 p.2) := by sorry
end TPG
