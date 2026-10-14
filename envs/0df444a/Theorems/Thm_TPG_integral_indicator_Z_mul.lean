-- Prove2me | Theorems.Thm_TPG_integral_indicator_Z_mul
-- name    : TPG.integral_indicator_Z_mul
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:04:09.939081+00:00
-- url     : https://prove2.me/theorems/1bf632b3-1f54-4035-869e-78e5299218ca
-- title:
--   Restricting to $\{Z_u=z\}$ is the same as fixing the action at time $u$
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$, let $u<T$ and $z\in\{0,1\}$, and let $F$ be a measurable function of the trajectory that is integrable along every state–action path (as in `TPG.integral_trajLaw`). Write $q^{u\to z}$ for the sequence $q$ with $q_u$ replaced by $z$ (so the action at time $u$ is $z$ with probability one). Then
--
--   $$\mathbb E_q\bigl[\mathbf 1\{Z_u=z\}\,F\bigr]=\mathbb P_q(Z_u=z)\ \mathbb E_{q^{u\to z}}[F],\qquad \mathbb P_q(Z_u=1)=q_u,\quad \mathbb P_q(Z_u=0)=1-q_u .$$
--
--   This is the mechanism behind every conditional expectation given one action in the source: conditioning on $Z_u=z$ changes one coordinate of the randomization sequence and nothing else.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it expresses the independence of the Bernoulli assignments of §2.3, p. 9, used in the conditional expectations E_θ[Y_t | Z_u = z] of eq. (7), p. 13.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_indicator_Z_mul {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (u : Fin T) (z : Bool) (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    ∫ ω, (if Z u ω = z then F ω else 0) ∂(E.trajLaw T q)
      = (if z then q (u : ℕ) else 1 - q (u : ℕ))
          * ∫ ω, F ω ∂(E.trajLaw T (Function.update q (u : ℕ) (if z then 1 else 0))) := by sorry
end TPG
