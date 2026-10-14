-- Prove2me | Theorems.Thm_TPG_integral_head_mul_tail
-- name    : TPG.integral_head_mul_tail
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:56:16.282549+00:00
-- url     : https://prove2.me/theorems/7d160608-6f52-40d1-acc2-9506dca47efe
-- title:
--   Markov property of the trajectory law in product form
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   Consider the horizon $m+1+n$. The **head** of a trajectory is its first $m+1$ time steps $0,\dots,m$, and the **tail** is its last $n$ steps $m+1,\dots,m+n$, re-indexed from $0$. For a state $a$, let $\mathbb E^{(m+1,a)}$ denote expectation for the process restarted at time $m+1$ from the state $a$: kernels $P^{m+1+t}_z$, initial state $a$, treatment probabilities $q_{m+1+t}$, the same reward laws.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$, and let $F$ (a function of a trajectory of length $m+1$) and $G$ (a function of a trajectory of length $n$) be bounded and measurable. Then
--
--   $$\mathbb E_q\bigl[F(\text{head})\,G(\text{tail})\bigr]=\sum_{a\in S}\ \mathbb E_q\bigl[F\cdot P^{m}_{Z_m}(X_m,a)\bigr]\ \mathbb E^{(m+1,a)}[G],$$
--
--   where the first expectation on the right is taken for the horizon $m+1$.
--
--   In words: given the head, the state at time $m+1$ is drawn from the row $X_m$ of $P^m_{Z_m}$, and given that state the tail is an independent copy of the restarted process. Covariance decay, strong mixing and the martingale arguments of the mission all rest on this identity.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it formalizes the Markov property of §2.2, pp. 8–9, in the form used in Appendix F.1, p. 40 (E[B_j | F_i] = (P^{(i+1)→a_j} g_j)(X_{i+1})) and in the proof of Lemma 2, p. 28.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_head_mul_tail {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (m n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, F (headTraj (m + 1) n ω) * G (tailTraj (m + 1) n ω) ∂(E.trajLaw (m + 1 + n) q)
      = ∑ a : S,
          (∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) q))
            * ∫ ω, G ω ∂((E.shift (m + 1) a).trajLaw n (fun t => q (m + 1 + t))) := by sorry
end TPG
