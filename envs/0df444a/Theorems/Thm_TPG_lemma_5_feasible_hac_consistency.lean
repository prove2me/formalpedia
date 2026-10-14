-- Prove2me | Theorems.Thm_TPG_lemma_5_feasible_hac_consistency
-- name    : TPG.lemma_5_feasible_hac_consistency
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:16:15.327204+00:00
-- url     : https://prove2.me/theorems/05d7ea96-6d12-40f6-9bbc-d9e1e0e3d5ab
-- title:
--   Lemma 5 — the feasible HAC estimator is asymptotically equivalent to the ideal one under Cesàro-$L^2$ mean stability
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Asymptotic setting.** The truncation size $k\ge0$ is fixed and the horizon $T\to\infty$; for each $T$ the trajectory $(X_t,Z_t,Y_t)_{t<T}$ is generated under the experimental policy $\pi_{1/2}$. Assumption 1 holds for all times with one constant $\gamma\in(0,1)$. Write $w_t^{\mathrm{IPW}}=2(2Z_t-1)$ and
--   $$B_t=\sum_{i=\max(0,t-k)}^{t}w_i^{\mathrm{IPW}}\,Y_t,\qquad \mu_t=\mathbb E[B_t],\qquad \bar B=\frac1T\sum_{t<T}B_t=\widehat\tau_k .$$
--   **Assumption 2 (asymptotic variance):** $\frac1T\operatorname{Var}\bigl(\sum_{t<T}B_t\bigr)\to\sigma_k^2$ as $T\to\infty$, with $0<\sigma_k^2<\infty$.
--
--   **Assumption 3 (Cesàro-$L^2$ mean stability):** with $\bar\mu_T=\frac1T\sum_{t<T}\mu_t$, $\ \Delta_T^2=\frac1T\sum_{t<T}(\mu_t-\bar\mu_T)^2=o(T^{-2/3})$.
--
--   The bandwidth $L_T$ is a deterministic integer sequence with $0\le L_T<T$ for every $T\ge1$, $L_T\to\infty$ and $L_T=O(T^{1/3})$, and $w_\ell^{\mathrm{NW}}=1-\ell/(L_T+1)$.
--
--   With $\widehat V_t=B_t-\bar B$ and $V_t=B_t-\mu_t$, define
--
--   $$\widehat\Gamma_\ell=\frac1T\sum_{t+\ell<T}\widehat V_t\,\widehat V_{t+\ell},\quad \widehat\Omega_T=\widehat\Gamma_0+2\sum_{\ell=1}^{L_T}w_\ell^{\mathrm{NW}}\,\widehat\Gamma_\ell,\qquad \widetilde\Gamma_\ell=\frac1T\sum_{t+\ell<T}V_t\,V_{t+\ell},\quad \widetilde\Omega_T=\widetilde\Gamma_0+2\sum_{\ell=1}^{L_T}w_\ell^{\mathrm{NW}}\,\widetilde\Gamma_\ell .$$
--
--   **Lemma.** Under Assumptions 1, 2 and 3, $\widehat\Omega_T-\widetilde\Omega_T=o_p(1)$ as $T\to\infty$.
--
--   The lemma justifies replacing the unknown time-specific means by the sample mean, which is what makes the variance estimator computable from a single trajectory.
--
--   **Formalization Note** $o_p(1)$ is stated as $\mathbb P(|\widehat\Omega_T-\widetilde\Omega_T|\ge\varepsilon)\to0$ for every $\varepsilon>0$, with the probability taken under the horizon-$T$ law. The limit $\sigma_k^2$ of Assumption 2 is a parameter $v$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix F.2, p. 42, Lemma 5; proof in Appendix H.3, pp. 54–55.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem lemma_5_feasible_hac_consistency {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hstab : E.MeanStability k) (hL : IsBandwidth L) :
    E.TendstoInProb
      (fun (T : ℕ) (ω : Traj S T) => hacEst T k (L T) ω - E.hacIdeal T k (L T) ω) 0 := by sorry
end TPG
