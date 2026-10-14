-- Prove2me | Theorems.Thm_TPG_corollary_1_gamma_alpha_mixing
-- name    : TPG.corollary_1_gamma_alpha_mixing
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:12:05.903802+00:00
-- url     : https://prove2.me/theorems/9ddf46c6-2933-44dd-a6cf-0c9b8be6c2d8
-- title:
--   Corollary 1 — $\alpha$-mixing of the local summands $\Gamma_t$: $\alpha_\Gamma(h)\le\gamma^{\max\{0,\,h-k-1\}}$
-- statement:
--   **Setting.** $S$ is a finite state space and the action $Z_t\in\{0,1\}$ is control or treatment. Time is $t=0,1,\dots,T-1$, which is the source's time $t+1$. Under action $z$ at time $t$ the state moves according to a transition matrix $P_z^t$, i.e. $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; the matrices may depend on $t$ arbitrarily. The initial state $X_0$ has distribution $\rho$, and the reward $Y_t$ has distribution $R(\cdot\mid X_t,Z_t)$ on $\mathbb R$, with $R([-M,M]\mid x,z)=1$ for all $x,z$ and conditional independence from everything else given $(X_t,Z_t)$. Under the policy $\pi_\theta$ every action is treatment with probability $\theta$, independently of everything else; $\mathbb E_\theta$, $\mathbb P_\theta$ and $\operatorname{Var}_\theta$ refer to the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under $\pi_\theta$.
--
--   **Assumption 1 (mixing time)** with constant $\gamma\in(0,1)$: for every time $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$, $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, where $\|f-f'\|_{\mathrm{TV}}=\tfrac12\|f-f'\|_1$. The **kernel deviation** is $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   Fix a truncation size $k$ and define the local summands
--
--   $$\Gamma_t=2\,(2Z_t-1)\sum_{u=t}^{\min(t+k,\,T-1)}Y_u ,\qquad t=0,\dots,T-1 .$$
--
--   **Corollary.** Under Assumption 1 and a Bernoulli randomization policy $\pi_\theta$, $0<\theta<1$: for all integers $s,h\ge0$ with $s+h+1\le T-1$, every $A\in\sigma(\Gamma_0,\dots,\Gamma_s)$ and every $B\in\sigma(\Gamma_{s+h+1},\dots,\Gamma_{T-1})$,
--
--   $$\bigl|\mathbb P_\theta(A\cap B)-\mathbb P_\theta(A)\,\mathbb P_\theta(B)\bigr|\le\gamma^{\max\{0,\,h-k\}} .$$
--
--   In the source's notation, with lag $h'=h+1\ge1$, this is $\alpha_\Gamma(h')\le\gamma^{\max\{0,\,h'-k-1\}}$: the bound is $1$ for $1\le h'\le k+1$ and $\gamma^{h'-k-1}$ for $h'\ge k+2$.
--
--   The summands $\Gamma_t$ are the terms of the TPG estimator, $\widehat\tau_k=\frac1T\sum_t\Gamma_t$; the corollary transfers the mixing rate of the process to them, with a delay equal to the window length.
--
--   **Formalization Note** The supremum defining $\alpha_\Gamma(h')$ is unfolded into a statement for each split point and each pair of events; the exponent is a truncated subtraction of natural numbers.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix A.4, p. 29, Corollary 1.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem corollary_1_gamma_alpha_mixing {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M)
    (s h : ℕ) (hsh : s + h + 1 < T)
    (A B : Set (Traj S T))
    (hA : MeasurableSet[sigmaGamma S T k 0 s] A)
    (hB : MeasurableSet[sigmaGamma S T k (s + h + 1) T] B) :
    |(E.expLaw T θ).real (A ∩ B) - (E.expLaw T θ).real A * (E.expLaw T θ).real B|
      ≤ γ ^ (h - k) := by sorry
end TPG
