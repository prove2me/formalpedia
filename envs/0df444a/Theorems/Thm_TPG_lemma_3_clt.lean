-- Prove2me | Theorems.Thm_TPG_lemma_3_clt
-- name    : TPG.lemma_3_clt
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:15:00.257756+00:00
-- url     : https://prove2.me/theorems/b59ce88d-8e66-48c1-8ff4-b9442c94014a
-- title:
--   Lemma 3 — central limit theorem for the TPG estimator
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Asymptotic setting.** The truncation size $k\ge0$ is fixed and the horizon $T\to\infty$; for each $T$ the trajectory $(X_t,Z_t,Y_t)_{t<T}$ is generated under the experimental policy $\pi_{1/2}$. Assumption 1 holds for all times with one constant $\gamma\in(0,1)$. Write $w_t^{\mathrm{IPW}}=2(2Z_t-1)$ and
--   $$B_t=\sum_{i=\max(0,t-k)}^{t}w_i^{\mathrm{IPW}}\,Y_t,\qquad \mu_t=\mathbb E[B_t],\qquad \bar B=\frac1T\sum_{t<T}B_t=\widehat\tau_k .$$
--   **Assumption 2 (asymptotic variance):** $\frac1T\operatorname{Var}\bigl(\sum_{t<T}B_t\bigr)\to\sigma_k^2$ as $T\to\infty$, with $0<\sigma_k^2<\infty$.
--
--   **Lemma.** Under Assumptions 1 and 2, as $T\to\infty$,
--
--   $$\sqrt T\,\bigl(\widehat\tau_k-\mathbb E[\widehat\tau_k]\bigr)\ \Rightarrow\ \mathcal N\bigl(0,\sigma_k^2\bigr),$$
--
--   where $\widehat\tau_k=\frac1T\sum_{u=0}^{T-1}\bigl(\frac{\mathbf 1\{Z_u=1\}}{1/2}-\frac{\mathbf 1\{Z_u=0\}}{1/2}\bigr)\sum_{t=u}^{\min(u+k,\,T-1)}Y_t$ is the TPG estimator.
--
--   This is the asymptotic normality part of Theorem 2; it does not need the mean-stability condition.
--
--   **Formalization Note** Convergence in distribution is stated as convergence of $\mathbb E[f(\cdot)]$ for every bounded continuous $f$, with the expectation taken under the horizon-$T$ law for each $T$. The limit $\sigma_k^2$ is a parameter $v$ constrained by Assumption 2.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix F.2, p. 41, Lemma 3; proof in Appendix H.1, pp. 51–53 (uses Definition 1 and Lemma 6, p. 51).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem lemma_3_clt {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) :
    E.TendstoNormal
      (fun (T : ℕ) (ω : Traj S T) =>
        Real.sqrt (T : ℝ) *
          (tpgEst (1 / 2) T k ω - ∫ ω', tpgEst (1 / 2) T k ω' ∂(E.expLaw T (1 / 2))))
      v := by sorry
end TPG
