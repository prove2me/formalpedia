-- Prove2me | Theorems.Thm_TPG_integral_trajLaw
-- name    : TPG.integral_trajLaw
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:50:47.355544+00:00
-- url     : https://prove2.me/theorems/0c8b181c-ad6b-4c3f-9005-5ce93b7459ee
-- title:
--   Integration against the trajectory law: $\mathbb E_q[F]=\sum_{x,z}w_q(x,z)\int F(x,z,y)\,\bigotimes_t R(dy_t\mid x_t,z_t)$
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$, let $F$ be a measurable real function of the trajectory, and suppose that for every state path $x$ and action path $z$ the function $y\mapsto F\bigl((x_t,z_t,y_t)_{t<T}\bigr)$ is integrable with respect to $\bigotimes_{t<T}R(\cdot\mid x_t,z_t)$. Then $F$ is integrable under $\mathbb P_q$ and
--
--   $$\mathbb E_q[F]=\sum_{x\in S^T}\ \sum_{z\in\{0,1\}^T}w_q(x,z)\int F\bigl((x_t,z_t,y_t)_{t<T}\bigr)\,\bigotimes_{t<T}R(dy_t\mid x_t,z_t),$$
--
--   with the path weight
--
--   $$w_q(x,z)=\rho(x_0)\prod_{s+1<T}P^s_{z_s}(x_s,x_{s+1})\prod_{t<T}q_t^{\,z_t}(1-q_t)^{1-z_t}$$
--
--   Every expectation in the mission is computed through this formula.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the expectation formula implied by the model of §2.2, pp. 8–9.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_trajLaw {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    Integrable F (E.trajLaw T q)
      ∧ ∫ ω, F ω ∂(E.trajLaw T q)
        = ∑ p : (Fin T → S) × (Fin T → Bool),
            E.pathWeight T q p.1 p.2 * ∫ y, F (embedPath p.1 p.2 y) ∂(E.rewardLaw p.1 p.2) := by sorry
end TPG
