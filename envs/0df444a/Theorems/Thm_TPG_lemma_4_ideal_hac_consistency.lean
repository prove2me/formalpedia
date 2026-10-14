-- Prove2me | Theorems.Thm_TPG_lemma_4_ideal_hac_consistency
-- name    : TPG.lemma_4_ideal_hac_consistency
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:15:38.576289+00:00
-- url     : https://prove2.me/theorems/3574e7f5-85f1-4419-824f-c0218f1c4ff5
-- title:
--   Lemma 4 — consistency of the ideal HAC estimator $\widetilde\Omega_T$
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Asymptotic setting.** The truncation size $k\ge0$ is fixed and the horizon $T\to\infty$; for each $T$ the trajectory $(X_t,Z_t,Y_t)_{t<T}$ is generated under the experimental policy $\pi_{1/2}$. Assumption 1 holds for all times with one constant $\gamma\in(0,1)$. Write $w_t^{\mathrm{IPW}}=2(2Z_t-1)$ and
--   $$B_t=\sum_{i=\max(0,t-k)}^{t}w_i^{\mathrm{IPW}}\,Y_t,\qquad \mu_t=\mathbb E[B_t],\qquad \bar B=\frac1T\sum_{t<T}B_t=\widehat\tau_k .$$
--   **Assumption 2 (asymptotic variance):** $\frac1T\operatorname{Var}\bigl(\sum_{t<T}B_t\bigr)\to\sigma_k^2$ as $T\to\infty$, with $0<\sigma_k^2<\infty$.
--
--   The bandwidth $L_T$ is a deterministic integer sequence with $0\le L_T<T$ for every $T\ge1$, $L_T\to\infty$ and $L_T=O(T^{1/3})$, and $w_\ell^{\mathrm{NW}}=1-\ell/(L_T+1)$.
--
--   The **ideal HAC estimator** centers at the time-specific means: with $V_t=B_t-\mathbb E[B_t]$,
--
--   $$\widetilde\Gamma_\ell=\frac1T\sum_{t+\ell<T}V_t\,V_{t+\ell},\qquad \widetilde\Omega_T=\widetilde\Gamma_0+2\sum_{\ell=1}^{L_T}w_\ell^{\mathrm{NW}}\,\widetilde\Gamma_\ell .$$
--
--   **Lemma.** Under Assumptions 1 and 2, $\widetilde\Omega_T\xrightarrow{p}\sigma_k^2$ as $T\to\infty$.
--
--   The ideal estimator is not computable from data, since the means $\mathbb E[B_t]$ are unknown; the lemma is the first step of the consistency proof for the feasible estimator of Theorem 2.
--
--   **Formalization Note** Convergence in probability is stated as $\mathbb P(|\widetilde\Omega_T-\sigma_k^2|\ge\varepsilon)\to0$ for every $\varepsilon>0$, with the probability taken under the horizon-$T$ law. The limit $\sigma_k^2$ is a parameter $v$ constrained by Assumption 2.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix F.2, p. 42, Lemma 4; proof in Appendix H.2, pp. 53–54.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem lemma_4_ideal_hac_consistency {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hL : IsBandwidth L) :
    E.TendstoInProb (fun (T : ℕ) (ω : Traj S T) => E.hacIdeal T k (L T) ω) v := by sorry
end TPG
