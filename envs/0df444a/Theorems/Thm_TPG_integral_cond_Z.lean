-- Prove2me | Theorems.Thm_TPG_integral_cond_Z
-- name    : TPG.integral_cond_Z
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:20:52.878208+00:00
-- url     : https://prove2.me/theorems/9755dee1-09c5-4ed8-a86f-dce5a7c6fef9
-- title:
--   Conditioning the trajectory law on one action: $\mathbb E_q[F\mid Z_u=z]=\mathbb E_{q^{u\to z}}[F]$
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$, let $u<T$ with $0<q_u<1$, let $z\in\{0,1\}$, and let $F$ be a measurable function of the trajectory that is integrable along every state–action path. Then the expectation of $F$ under the conditional law given $\{Z_u=z\}$ is the expectation under the law in which the action at time $u$ is $z$ with probability one:
--
--   $$\mathbb E_q[F\mid Z_u=z]=\mathbb E_{q^{u\to z}}[F],$$
--
--   where $q^{u\to z}$ is $q$ with $q_u$ replaced by $z\in\{0,1\}$.
--
--   With $F=Y_t$ this turns the $Q$-values of the source into expected rewards under modified randomization sequences.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it identifies the conditional expectations E_θ[Y_t | Z_u = z] of eqs. (7) and (10), pp. 13 and 15.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_cond_Z {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (u : Fin T) (z : Bool) (hu : 0 < q (u : ℕ) ∧ q (u : ℕ) < 1)
    (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    ∫ ω, F ω ∂(ProbabilityTheory.cond (E.trajLaw T q) {ω | Z u ω = z})
      = ∫ ω, F ω ∂(E.trajLaw T (Function.update q (u : ℕ) (if z then 1 else 0))) := by sorry
end TPG
