-- Prove2me | Theorems.Thm_TPG_integral_head_mul_gap_tail
-- name    : TPG.integral_head_mul_gap_tail
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:26:00.526717+00:00
-- url     : https://prove2.me/theorems/5d5a0815-9f48-4407-8420-025651cc855a
-- title:
--   Markov property of the trajectory law across a gap of $h$ steps
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$. For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, $\mathbb P_q$ and $\mathbb E_q$ denote the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, $X_{t+1}\sim P^t_{Z_t}(X_t,\cdot)$, and the rewards are conditionally independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$ (`Env.trajLaw T q`); the Bernoulli policy $\pi_\theta$ is $q_t\equiv\theta$.
--
--   Consider the horizon $m+1+h+n$. The **head** is the first $m+1$ time steps $0,\dots,m$; after a **gap** of $h$ steps, the **tail** is the last $n$ steps $m+1+h,\dots,m+h+n$, re-indexed from $0$. Let $\Pi=P^{m+1}_{q_{m+1}}P^{m+2}_{q_{m+2}}\cdots P^{m+h}_{q_{m+h}}$ with $P^s_\theta=\theta P^s_1+(1-\theta)P^s_0$ (the identity when $h=0$), and for a state $b$ let $\mathbb E^{(m+1+h,b)}$ denote expectation for the process restarted at time $m+1+h$ from $b$.
--
--   **Lemma.** Let $0\le q_t\le1$ for all $t$, and let $F$ (a function of a trajectory of length $m+1$) and $G$ (a function of a trajectory of length $n$) be bounded and measurable. Then
--
--   $$\mathbb E_q\bigl[F(\text{head})\,G(\text{tail})\bigr]=\sum_{a\in S}\sum_{b\in S}\ \mathbb E_q\bigl[F\cdot P^{m}_{Z_m}(X_m,a)\bigr]\ \Pi(a,b)\ \mathbb E^{(m+1+h,b)}[G].$$
--
--   The head influences the tail only through the distribution of the state at time $m+1$, propagated by the $h$ intermediate kernels. Combined with the contraction of Assumption 1 this yields geometric decay of covariances between functions of time windows separated by $h$ steps, which is how the source obtains its variance bound and the strong mixing property.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it formalizes the identity E[B_j | F_i] = (P_{1/2}^{(i+1)→a_j} g_j)(X_{i+1}) of Appendix F.1, p. 40, and the conditioning step in the proof of Lemma 2, p. 28.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem integral_head_mul_gap_tail {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (m h n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, F (headTraj (m + 1) (h + n) ω) * G (tailTraj h n (tailTraj (m + 1) (h + n) ω))
        ∂(E.trajLaw (m + 1 + (h + n)) q)
      = ∑ a : S, ∑ b : S,
          (∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) q))
            * (((List.Ico (m + 1) (m + 1 + h)).map (fun s => E.PMix (q s) s)).prod a b)
            * ∫ ω, G ω ∂((E.shift (m + 1 + h) b).trajLaw n (fun t => q (m + 1 + h + t))) := by sorry
end TPG
