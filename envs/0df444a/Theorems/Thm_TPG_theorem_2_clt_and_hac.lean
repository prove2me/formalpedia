-- Prove2me | Theorems.Thm_TPG_theorem_2_clt_and_hac
-- name    : TPG.theorem_2_clt_and_hac
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:17:47.962139+00:00
-- url     : https://prove2.me/theorems/e2247c87-b544-4727-8ea5-482801e646b6
-- title:
--   Theorem 2 — central limit theorem for the TPG estimator and consistency of the nonstationary HAC variance estimator
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
--   With $\widehat V_t=B_t-\bar B$, the **nonstationary HAC variance estimator** is
--
--   $$\widehat\Gamma_\ell=\frac1T\sum_{t+\ell<T}\widehat V_t\,\widehat V_{t+\ell},\qquad \widehat\Omega_T=\widehat\Gamma_0+2\sum_{\ell=1}^{L_T}w_\ell^{\mathrm{NW}}\,\widehat\Gamma_\ell .$$
--
--   **Theorem.** Under Assumptions 1, 2 and 3, as $T\to\infty$,
--
--   $$\sqrt T\,\bigl(\widehat\tau_k-\mathbb E[\widehat\tau_k]\bigr)\ \Rightarrow\ \mathcal N\bigl(0,\sigma_k^2\bigr),\qquad \widehat\Omega_T\ \xrightarrow{p}\ \sigma_k^2 ,$$
--
--   where $\widehat\tau_k=\frac1T\sum_{u=0}^{T-1}\bigl(\frac{\mathbf 1\{Z_u=1\}}{1/2}-\frac{\mathbf 1\{Z_u=0\}}{1/2}\bigr)\sum_{t=u}^{\min(u+k,\,T-1)}Y_t$ is the TPG estimator.
--
--   The theorem gives an estimated standard error $\sqrt{\widehat\Omega_T/T}$ for the TPG estimator from a single nonstationary trajectory, and hence confidence intervals for $\mathbb E[\widehat\tau_k]$.
--
--   **Formalization Note** For each $T$ the statistics are computed under the horizon-$T$ law. Convergence in distribution is stated as convergence of $\mathbb E[f(\cdot)]$ for every bounded continuous $f$, and convergence in probability as $\mathbb P(|\widehat\Omega_T-\sigma_k^2|\ge\varepsilon)\to0$ for every $\varepsilon>0$. The limit $\sigma_k^2$ is a parameter $v$ constrained by Assumption 2.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §6 (Nonstationary CLT and variance estimation), p. 17, Assumptions 2–3 and Theorem 2; proof in Appendix F.2, pp. 41–42, via Lemmas 3–5.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem theorem_2_clt_and_hac {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hstab : E.MeanStability k) (hL : IsBandwidth L) :
    E.TendstoNormal
        (fun (T : ℕ) (ω : Traj S T) =>
          Real.sqrt (T : ℝ) *
            (tpgEst (1 / 2) T k ω - ∫ ω', tpgEst (1 / 2) T k ω' ∂(E.expLaw T (1 / 2))))
        v
      ∧ E.TendstoInProb (fun (T : ℕ) (ω : Traj S T) => hacEst T k (L T) ω) v := by sorry
end TPG
