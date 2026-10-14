-- Prove2me | Theorems.Thm_TPG_integral_fun_state_action
-- name    : TPG.integral_fun_state_action
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:15:37.288148+00:00
-- url     : https://prove2.me/theorems/29e68a73-df09-4ea1-ba0c-90435931f357
-- title:
--   Joint law of the state and action at one time: $X_t\sim\mu_q^t$, $Z_t\sim\mathrm{Bernoulli}(q_t)$ independent
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$. For every time $t<T$ and every function $g:S\times\{0,1\}\to\mathbb R$,
--
--   $$\mathbb E_q\bigl[g(X_t,Z_t)\bigr]=\sum_{a\in S}\mu_q^t(a)\,\bigl(q_t\,g(a,1)+(1-q_t)\,g(a,0)\bigr),\qquad \mu_q^t=\rho^\top P^0_{q_0}P^1_{q_1}\cdots P^{t-1}_{q_{t-1}} .$$
--
--   So $X_t$ has distribution $\mu_q^t$ and $Z_t$ is an independent Bernoulli$(q_t)$ variable. This is the one-time marginal behind all first-moment computations.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the marginal distribution of (X_t, Z_t) implied by the model of §2.2–2.3, pp. 8–9, in the notation μ_q^t = ρ^⊤ P_q^{1→t} of Appendix D, p. 31.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_fun_state_action {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (t : Fin T) (g : S → Bool → ℝ) :
    ∫ ω, g (X t ω) (Z t ω) ∂(E.trajLaw T q)
      = ∑ a : S, E.stateVec q (t : ℕ) a
          * (q (t : ℕ) * g a true + (1 - q (t : ℕ)) * g a false) := by sorry
end TPG
